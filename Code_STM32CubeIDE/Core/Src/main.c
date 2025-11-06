/* USER CODE BEGIN Header */
/*
  *******************************************************************************
  * File   : main.c
  * Brief  : STM32 <-> HM10 with fixed-width S/K frames + ADC(HW-080) + DHT11
  *******************************************************************************
  * Giao thuc:
  *   RX (ESP32 -> STM32):  '1','0','A','M'  (1 byte ASCII; chap nhan 'a'/'m')
  *   TX (STM32 -> ESP32):  type y z ttt TTT '\n'  (fixed width)
  *                         type in {'S','K'}
  *                         y=0|1 (pump), z in {'A','M'}, ttt=000..100 (soil %),
  *                         TTT=000..099 (degC)
  *   Vi du: S1A057031\n, K0M063028\n
  *
  * Gui lenh:
  * - Gui S... khi thay doi dang ke (delta pct >= 2 hoac pump/mode doi) va cach nhau >= 500 ms
  * - Gui K... ngay sau khi ap dung lenh
  * - Log theo BLOCK it - ro (6 dong + 1 dong trong) qua UART2 115200
  *******************************************************************************/
/* USER CODE END Header */

/* Includes ------------------------------------------------------------------*/
#include "main.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>

/* ===================== CONFIG ===================== */
#define N_SAMPLES              16U       // So mau ADC lay trung binh
#define UI_LOG_PERIOD_MS       3000U     // In 1 block / 3s
#define S_MIN_PERIOD_MS        500U      // Khoang cach toi thieu 2 khung S
#define DELTA_PCT_TO_SEND      2
#define TH_LOW_DEFAULT         30U
#define TH_HIGH_DEFAULT        40U

/* Hieu chuan HW-080 (ADC 12b: 0..4095) */
#define DRY_ADC                3600U     // ADC khi cam bien kho
#define WET_ADC                1000U     // ADC khi dat rat uot/nhung nuoc

/* DHT11 */
#define DHT_MIN_INTERVAL_MS    1000U
#define DHT_TEMP_OFFSET_C      0         // Cong bu nhiet neu can (+/-)
/* ================================================== */

#define BLE_WINDOW_SIZE         5U      // 10 mau trong 2 s
#define BLE_SAMPLE_PERIOD_MS    400U     // 200 ms/mau
#define BLE_HIGH_THRESHOLD      3U       // >=8/10 HIGH => coi như connected


/* Private variables ---------------------------------------------------------*/
ADC_HandleTypeDef  hadc1;
UART_HandleTypeDef huart1;  // HM10 9600
UART_HandleTypeDef huart2;  // Console 115200
TIM_HandleTypeDef  htim2;   // 1 MHz cho DHT11

/* ===== STATE (he thong) ===== */
static volatile uint8_t  pump_on    = 0;   // 1=ON
static volatile uint8_t  mode_auto  = 1;   // 1=AUTO, 0=MANUAL
static volatile uint8_t  pct        = 0;   // 0..100
static volatile uint8_t  tempC      = 0;   // 0..99

/* ===== Debug/raw ===== */
static uint32_t last_adc_raw   = 0;
static uint8_t  last_pct_quick = 0;
static uint8_t  last_dht[5]    = {0};
static uint8_t  last_dht_ok    = 0;

/* ===== TX/RX snapshot cho 1 block log ===== */
static char     last_tx_frame[16] = {0};
static uint8_t  tx_pending        = 0;
static uint8_t  last_rx_byte      = 0;
static uint8_t  rx_pending        = 0;

/* ===== BLE STATE (PB5) loc on dinh >=300ms ===== */
static uint8_t  ble_sample_last    = 0;
static uint8_t  ble_state_filtered = 0;
static uint32_t ble_change_ms      = 0;

/* ===== BLE moving-average window (2s) ===== */
static uint8_t  ble_hist[BLE_WINDOW_SIZE] = {0};
static uint8_t  ble_hist_idx   = 0;      // chỉ số vòng tròn 0..BLE_WINDOW_SIZE-1
static uint8_t  ble_hist_count = 0;      // số mẫu đã tích lũy (tối đa = window size)
static uint8_t  ble_hist_sum   = 0;      // tổng số mẫu =1 trong cửa sổ
static uint32_t ble_last_sample_ms = 0;  // mốc thời gian cho bước lấy mẫu mỗi 200 ms


/* ===== Prototypes ===== */
void        SystemClock_Config(void);
static void MX_GPIO_Init(void);
static void MX_USART2_UART_Init(void);
static void MX_USART1_UART_Init(void);
static void MX_ADC1_Init(void);
static void MX_TIM2_Init(void);

/* Giao thuc */
static void HM10_Receive_1Char(void);
static void HM10_Send_Frame(char type);     // 'S' hoac 'K'
static void apply_command(uint8_t c);

/* Sensor utils */
static uint32_t readA0(void);
static uint32_t readA0_avg(uint8_t n);
static uint8_t  moisture_pct_from_adc(uint32_t adc);
static inline void Pump_On(void);
static inline void Pump_Off(void);

/* printf -> UART2 */
int __io_putchar(int ch);

/* DHT11 (TIM2 1MHz) */
static inline uint32_t micros(void);
static void delay_us(uint32_t us);
static void dht11_pin_output(void);
static void dht11_pin_input_pullup(void);
static uint8_t dht11_read_once(int *tC, int *humi);
static void DHT11_Update_Periodic(void);

/* Hysteresis theo nhiet do */
static void thresholds_by_temp(uint8_t tC, uint8_t *thL, uint8_t *thH);

/* Log block gon: 6 dong + 1 dong trong */
static void print_status_block(uint8_t ble_state, uint8_t thL, uint8_t thH);

/* ===================== Retarget printf ===================== */
int __io_putchar(int ch)
{
  HAL_UART_Transmit(&huart2, (uint8_t*)&ch, 1, HAL_MAX_DELAY);
  return ch;
}

/* ===================== ADC / Soil ===================== */
static uint32_t readA0(void)
{
  HAL_ADC_Start(&hadc1);
  HAL_ADC_PollForConversion(&hadc1, 10);
  uint32_t v = HAL_ADC_GetValue(&hadc1);
  HAL_ADC_Stop(&hadc1);
  return v;
}
static uint32_t readA0_avg(uint8_t n)
{
  uint32_t s = 0;
  for (uint8_t i = 0; i < n; i++) { s += readA0(); HAL_Delay(2); }
  return s / n;
}
static uint8_t moisture_pct_from_adc(uint32_t adc)
{
  last_adc_raw = adc;
  // % nhanh (khong hieu chuan)
  last_pct_quick = 100 - (uint8_t)((adc * 100U) / 4095U);

  // noi suy 2 diem DRY/WET
  if (adc > DRY_ADC) adc = DRY_ADC;
  if (adc < WET_ADC) adc = WET_ADC;
  uint32_t num = (DRY_ADC - adc) * 100U;
  uint32_t den = (DRY_ADC - WET_ADC);
  uint32_t p   = den ? (num / den) : 0U;
  if (p > 100U) p = 100U;
  return (uint8_t)p;
}
static inline void Pump_On(void)
{
  HAL_GPIO_WritePin(RELAY_Pin_GPIO_Port, RELAY_Pin_Pin, GPIO_PIN_SET);
  pump_on = 1;
}
static inline void Pump_Off(void)
{
  HAL_GPIO_WritePin(RELAY_Pin_GPIO_Port, RELAY_Pin_Pin, GPIO_PIN_RESET);
  pump_on = 0;
}

/* ===================== Frames TX ===================== */
/* "%c%d%c%03u%03u\n" -> type y z ttt TTT \n */
static void HM10_Send_Frame(char type)
{
  char z = mode_auto ? 'A' : 'M';
  uint8_t pct_send  = (pct   > 100) ? 100 : pct;
  uint8_t temp_send = (tempC >  99) ?  99 : tempC;

  char frame[16];
  int n = snprintf(frame, sizeof(frame), "%c%d%c%03u%03u\n",
                   type, pump_on, z, (unsigned)pct_send, (unsigned)temp_send);
  if (n <= 0) return;

  // Gửi 3 gói liên tục, cách nhau 50ms để ESP32 dễ nhận
  for (int i = 0; i < 2; i++) {
    if (HAL_UART_Transmit(&huart1, (uint8_t*)frame, (uint16_t)n, 100) == HAL_OK) {
      strncpy(last_tx_frame, frame, sizeof(last_tx_frame)-1);
      tx_pending = 1;
    }
    HAL_Delay(50);  // delay goi tin
  }
}


/* Ap dung lenh 1 byte va gui ACK K... ngay */
static void apply_command(uint8_t c)
{
  switch (c)
  {
    case '1': Pump_On();     break;
    case '0': Pump_Off();    break;
    case 'A': mode_auto = 1; break;
    case 'M': mode_auto = 0; break;
    default:  return; // khong hop le
  }
  HM10_Send_Frame('K');  // ACK ngay
}

/* ===================== RX 1 BYTE (UTF-8 tolerant) ===================== */
static void HM10_Receive_1Char(void)
{
  uint8_t b;
  while (HAL_UART_Receive(&huart1, &b, 1, 0) == HAL_OK)
  {
    // bo qua ki tu trang thai/phu
    if (b==0x00 || b=='\r' || b=='\n' || b=='\t' || b==' ') continue;
    // non-ASCII (UTF-8 continuation / fullwidth)
    if (b >= 0x80) continue;
    // chap nhan a/m
    if (b=='a') b='A';
    if (b=='m') b='M';

    // luu RX cho block
    last_rx_byte = b;
    rx_pending   = 1;

    if (b=='0' || b=='1' || b=='A' || b=='M') {
      apply_command(b);
    }
  }
}

/* ===================== DHT11 (TIM2 1MHz) ===================== */
static inline uint32_t micros(void) { return __HAL_TIM_GET_COUNTER(&htim2); }
static void delay_us(uint32_t us)
{
  uint32_t t0 = micros();
  while ((uint32_t)(micros() - t0) < us) { __NOP(); }
}
static void dht11_pin_output(void)
{
  GPIO_InitTypeDef s = {0};
  s.Pin = DHT11_Pin_Pin; s.Mode = GPIO_MODE_OUTPUT_PP; s.Pull = GPIO_NOPULL; s.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(DHT11_Pin_GPIO_Port, &s);
}
static void dht11_pin_input_pullup(void)
{
  GPIO_InitTypeDef s = {0};
  s.Pin = DHT11_Pin_Pin; s.Mode = GPIO_MODE_INPUT; s.Pull = GPIO_PULLUP;
  HAL_GPIO_Init(DHT11_Pin_GPIO_Port, &s);
}
static uint8_t wait_level(GPIO_TypeDef* port, uint16_t pin, GPIO_PinState lvl, uint32_t tout_us)
{
  uint32_t t0 = micros();
  while (HAL_GPIO_ReadPin(port, pin) != lvl) {
    if ((uint32_t)(micros() - t0) > tout_us) return 0;
  }
  return 1;
}
static uint8_t dht11_read_once(int *tC, int *humi)
{
  uint8_t d[5] = {0};

  // start 18ms
  dht11_pin_output();
  HAL_GPIO_WritePin(DHT11_Pin_GPIO_Port, DHT11_Pin_Pin, GPIO_PIN_RESET);
  HAL_Delay(18);
  HAL_GPIO_WritePin(DHT11_Pin_GPIO_Port, DHT11_Pin_Pin, GPIO_PIN_SET);
  delay_us(30);
  dht11_pin_input_pullup();

  if (!wait_level(DHT11_Pin_GPIO_Port, DHT11_Pin_Pin, GPIO_PIN_RESET, 120)) return 0;
  if (!wait_level(DHT11_Pin_GPIO_Port, DHT11_Pin_Pin, GPIO_PIN_SET,   120)) return 0;
  if (!wait_level(DHT11_Pin_GPIO_Port, DHT11_Pin_Pin, GPIO_PIN_RESET, 120)) return 0;

  for (int i=0;i<40;i++) {
    if (!wait_level(DHT11_Pin_GPIO_Port, DHT11_Pin_Pin, GPIO_PIN_SET, 120)) return 0;
    uint32_t t = micros();
    if (!wait_level(DHT11_Pin_GPIO_Port, DHT11_Pin_Pin, GPIO_PIN_RESET, 120)) return 0;
    uint32_t w = (uint32_t)(micros() - t);
    uint8_t bit = (w > 50) ? 1 : 0;
    d[i/8] <<= 1; d[i/8] |= bit;
  }
  if ((uint8_t)(d[0]+d[1]+d[2]+d[3]) != d[4]) return 0;

  memcpy((void*)last_dht, d, 5); last_dht_ok = 1;
  *humi = d[0];
  *tC   = d[2];
  return 1;
}
static void DHT11_Update_Periodic(void)
{
  static uint32_t t_last = 0;
  uint32_t now = HAL_GetTick();
  if (now - t_last < DHT_MIN_INTERVAL_MS) return;
  t_last = now;

  int t=0,h=0;
  if (dht11_read_once(&t,&h)) {
    int t_adj = t + DHT_TEMP_OFFSET_C;
    if (t_adj < 0) t_adj = 0; if (t_adj > 99) t_adj = 99;
    tempC = (uint8_t)t_adj;
  } else {
    last_dht_ok = 0;
  }
}

/* ===================== Hysteresis by temperature ===================== */
static void thresholds_by_temp(uint8_t tC, uint8_t *thL, uint8_t *thH)
{
  if (tC <= 15)      { *thL = 25; *thH = 35; }
  else if (tC < 30)  { *thL = 30; *thH = 40; }
  else               { *thL = 35; *thH = 45; }
}

/* ===================== Log block gon ===================== */
static void print_status_block(uint8_t ble_state, uint8_t thL, uint8_t thH)
{
  // 1) RAW-SOIL
  printf("[RAW-SOIL] ADC=%lu DRY=%lu WET=%lu\r\n",
         (unsigned long)last_adc_raw, (unsigned long)DRY_ADC, (unsigned long)WET_ADC);

  // 2) RAW-DHT
  printf("[RAW-DHT ] bytes=%02X %02X %02X %02X %02X ok=%u Traw=%u\r\n",
         last_dht[0], last_dht[1], last_dht[2], last_dht[3], last_dht[4],
         (unsigned)last_dht_ok, (unsigned)last_dht[2]);

  // 3) CAL-SOIL
  printf("[CAL-SOIL] pct_quick=%03u pct_cal=%03u\r\n",
         (unsigned)last_pct_quick, (unsigned)pct);

  // 4) CAL-DHT
  printf("[CAL-DHT ] Tcal=%03u offset=%d\r\n", (unsigned)tempC, (int)DHT_TEMP_OFFSET_C);

  // 5) STAT
  printf("[STAT    ] pump=%u mode=%c pct=%03u T=%03u BLE=%u thL=%u thH=%u\r\n",
         pump_on?1:0, mode_auto?'A':'M', (unsigned)pct, (unsigned)tempC,
         (unsigned)ble_state, (unsigned)thL, (unsigned)thH);

  // 6) TX/RX
  if (tx_pending) {
    size_t n = strcspn(last_tx_frame, "\r\n");
    printf("[TX      ] %.*s\r\n", (int)n, last_tx_frame);
    tx_pending = 0; last_tx_frame[0] = 0;
  } else {
    printf("[TX      ] NONE\r\n");
  }
  if (rx_pending) {
    printf("[RX      ] 0x%02X '%c'\r\n", (unsigned)last_rx_byte,
           (last_rx_byte>=32&&last_rx_byte<=126)?last_rx_byte:'.');
    rx_pending = 0;
  } else {
    printf("[RX      ] NONE\r\n");
  }

  // 7) dong trong
  printf("\r\n");
}

/* ===================== MAIN ===================== */
int main(void)
{
  HAL_Init();
  SystemClock_Config();
  MX_GPIO_Init();
  MX_USART2_UART_Init();   // Putty 115200 - Asynchronous
  MX_USART1_UART_Init();   // HM10  9600   - Asynchronous
  MX_ADC1_Init();
  MX_TIM2_Init();          // for DHT11 us timing

  HAL_TIM_Base_Start(&htim2);

  // Khoi tao BLE filtered tu PB5
  ble_sample_last    = (HAL_GPIO_ReadPin(BLE_STATE_Pin_GPIO_Port, BLE_STATE_Pin_Pin)==GPIO_PIN_SET)?1:0;
  ble_state_filtered = ble_sample_last;
  ble_change_ms      = HAL_GetTick();

  // Ban dau in 1 banner nho
  setvbuf(stdout, NULL, _IONBF, 0);
  printf("\r\n[BOOT] STM32 ready S/K + Soil + DHT11\r\n");
  printf("DRY_ADC=%lu WET_ADC=%lu DHT_TEMP_OFFSET=%d\r\n\r\n",
         (unsigned long)DRY_ADC, (unsigned long)WET_ADC, (int)DHT_TEMP_OFFSET_C);

  uint8_t  last_pct_sent  = 255;
  uint8_t  last_pump_sent = 2;
  uint8_t  last_mode_sent = 2;
  uint32_t last_tx_ms     = 0;
  uint32_t last_log_ms    = 0;
  uint8_t  last_temp_sent = 255;


  while (1)
  {
    // 1) Nhan lenh 1 byte (poll non-blocking)
    HM10_Receive_1Char();

    // 2) Doc cam bien
    uint32_t adc = readA0_avg(N_SAMPLES);
    pct = moisture_pct_from_adc(adc);
    DHT11_Update_Periodic();

    // 3) Hysteresis theo nhiet do
    uint8_t thL=TH_LOW_DEFAULT, thH=TH_HIGH_DEFAULT;
    thresholds_by_temp(tempC, &thL, &thH);
    if (mode_auto) {
      if (!pump_on && pct < thL)  { Pump_On(); HM10_Send_Frame('S');}
      if ( pump_on && pct > thH)  { Pump_Off(); HM10_Send_Frame('S');}
    }
    HAL_GPIO_WritePin(GPIOA, LD2_Pin, pump_on ? GPIO_PIN_SET : GPIO_PIN_RESET);

    // 4) BLE moving-average: 10 mau / 2s =>  BLE=0/1
    uint32_t now = HAL_GetTick();

    if ((now - ble_last_sample_ms) >= BLE_SAMPLE_PERIOD_MS) {
      ble_last_sample_ms = now;

      uint8_t s = (HAL_GPIO_ReadPin(BLE_STATE_Pin_GPIO_Port, BLE_STATE_Pin_Pin) == GPIO_PIN_SET) ? 1 : 0;

      uint8_t old = ble_hist[ble_hist_idx];
      ble_hist[ble_hist_idx] = s;
      ble_hist_idx++;
      if (ble_hist_idx >= BLE_WINDOW_SIZE) ble_hist_idx = 0;

      if (ble_hist_count < BLE_WINDOW_SIZE) {
        ble_hist_count++;
        ble_hist_sum += s;
      } else {
        if (old) ble_hist_sum--;
        if (s)   ble_hist_sum++;
      }

      if (ble_hist_count == BLE_WINDOW_SIZE) {
        uint8_t new_ble = (ble_hist_sum >= BLE_HIGH_THRESHOLD) ? 1 : 0;

        if (new_ble != ble_state_filtered) {
          ble_state_filtered = new_ble;

          if (ble_state_filtered == 1) {
            HM10_Send_Frame('S');
            last_tx_ms = now;
            last_pct_sent  = pct;
            last_pump_sent = pump_on;
            last_mode_sent = mode_auto;
          }

        }
      }
    }


    // 5) Gui S... khi thay doi dang ke (soil/pump/mode/temp) + rate limit
    if ( (abs((int)pct - (int)last_pct_sent)  >= DELTA_PCT_TO_SEND) ||   // pct
         (abs((int)tempC - (int)last_temp_sent) >= 1)                ||   // temperature
         (pump_on != last_pump_sent) || (mode_auto != last_mode_sent) ) {

      if (now - last_tx_ms >= S_MIN_PERIOD_MS) {
        HM10_Send_Frame('S');
        last_tx_ms      = now;
        last_pct_sent   = pct;
        last_temp_sent  = tempC;
        last_pump_sent  = pump_on;
        last_mode_sent  = mode_auto;
      }
    }


    // 6) In 1 block gon
    if (now - last_log_ms >= UI_LOG_PERIOD_MS) {
      last_log_ms = now;
      print_status_block(ble_state_filtered, thL, thH);
    }

    HAL_Delay(30);
  }
}

/* ===================== PERIPHERALS ===================== */
void SystemClock_Config(void)
{
  RCC_OscInitTypeDef RCC_OscInitStruct = {0};
  RCC_ClkInitTypeDef RCC_ClkInitStruct = {0};

  __HAL_RCC_PWR_CLK_ENABLE();
  __HAL_PWR_VOLTAGESCALING_CONFIG(PWR_REGULATOR_VOLTAGE_SCALE2);

  RCC_OscInitStruct.OscillatorType = RCC_OSCILLATORTYPE_HSI;
  RCC_OscInitStruct.HSIState = RCC_HSI_ON;
  RCC_OscInitStruct.PLL.PLLState = RCC_PLL_ON;
  RCC_OscInitStruct.PLL.PLLSource = RCC_PLLSOURCE_HSI;
  RCC_OscInitStruct.PLL.PLLM = 16;
  RCC_OscInitStruct.PLL.PLLN = 336;
  RCC_OscInitStruct.PLL.PLLP = RCC_PLLP_DIV4;
  RCC_OscInitStruct.PLL.PLLQ = 7;
  if (HAL_RCC_OscConfig(&RCC_OscInitStruct) != HAL_OK) { Error_Handler(); }

  RCC_ClkInitStruct.ClockType = RCC_CLOCKTYPE_HCLK|RCC_CLOCKTYPE_SYSCLK
                              |RCC_CLOCKTYPE_PCLK1|RCC_CLOCKTYPE_PCLK2;
  RCC_ClkInitStruct.SYSCLKSource   = RCC_SYSCLKSOURCE_PLLCLK;
  RCC_ClkInitStruct.AHBCLKDivider  = RCC_SYSCLK_DIV1;
  RCC_ClkInitStruct.APB1CLKDivider = RCC_HCLK_DIV2;
  RCC_ClkInitStruct.APB2CLKDivider = RCC_HCLK_DIV1;
  if (HAL_RCC_ClockConfig(&RCC_ClkInitStruct, FLASH_LATENCY_2) != HAL_OK) { Error_Handler(); }
}

static void MX_ADC1_Init(void)
{
  ADC_ChannelConfTypeDef sConfig = {0};
  hadc1.Instance                      = ADC1;
  hadc1.Init.ClockPrescaler           = ADC_CLOCK_SYNC_PCLK_DIV4;
  hadc1.Init.Resolution               = ADC_RESOLUTION_12B;
  hadc1.Init.ScanConvMode             = DISABLE;
  hadc1.Init.ContinuousConvMode       = DISABLE;
  hadc1.Init.DiscontinuousConvMode    = DISABLE;
  hadc1.Init.ExternalTrigConvEdge     = ADC_EXTERNALTRIGCONVEDGE_NONE;
  hadc1.Init.ExternalTrigConv         = ADC_SOFTWARE_START;
  hadc1.Init.DataAlign                = ADC_DATAALIGN_RIGHT;
  hadc1.Init.NbrOfConversion          = 1;
  hadc1.Init.DMAContinuousRequests    = DISABLE;
  hadc1.Init.EOCSelection             = ADC_EOC_SINGLE_CONV;
  if (HAL_ADC_Init(&hadc1) != HAL_OK) { Error_Handler(); }

  sConfig.Channel      = ADC_CHANNEL_0; /* PA0 */
  sConfig.Rank         = 1;
  sConfig.SamplingTime = ADC_SAMPLETIME_84CYCLES;
  if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK) { Error_Handler(); }
}

static void MX_TIM2_Init(void)
{
  TIM_ClockConfigTypeDef sClockSourceConfig = {0};
  TIM_MasterConfigTypeDef sMasterConfig = {0};

  htim2.Instance               = TIM2;
  htim2.Init.Prescaler         = 83;             /* 84MHz/84 = 1MHz */
  htim2.Init.CounterMode       = TIM_COUNTERMODE_UP;
  htim2.Init.Period            = 4294967295;
  htim2.Init.ClockDivision     = TIM_CLOCKDIVISION_DIV1;
  htim2.Init.AutoReloadPreload = TIM_AUTORELOAD_PRELOAD_DISABLE;
  if (HAL_TIM_Base_Init(&htim2) != HAL_OK) { Error_Handler(); }

  sClockSourceConfig.ClockSource = TIM_CLOCKSOURCE_INTERNAL;
  if (HAL_TIM_ConfigClockSource(&htim2, &sClockSourceConfig) != HAL_OK) { Error_Handler(); }

  sMasterConfig.MasterOutputTrigger = TIM_TRGO_RESET;
  sMasterConfig.MasterSlaveMode     = TIM_MASTERSLAVEMODE_DISABLE;
  if (HAL_TIMEx_MasterConfigSynchronization(&htim2, &sMasterConfig) != HAL_OK) { Error_Handler(); }
}

static void MX_USART1_UART_Init(void)
{
  huart1.Instance          = USART1;   /* HM10 */
  huart1.Init.BaudRate     = 9600;
  huart1.Init.WordLength   = UART_WORDLENGTH_8B;
  huart1.Init.StopBits     = UART_STOPBITS_1;
  huart1.Init.Parity       = UART_PARITY_NONE;
  huart1.Init.Mode         = UART_MODE_TX_RX;
  huart1.Init.HwFlowCtl    = UART_HWCONTROL_NONE;
  huart1.Init.OverSampling = UART_OVERSAMPLING_16;
  if (HAL_UART_Init(&huart1) != HAL_OK) { Error_Handler(); }
}

static void MX_USART2_UART_Init(void)
{
  huart2.Instance          = USART2;   /* Console Putty */
  huart2.Init.BaudRate     = 115200;
  huart2.Init.WordLength   = UART_WORDLENGTH_8B;
  huart2.Init.StopBits     = UART_STOPBITS_1;
  huart2.Init.Parity       = UART_PARITY_NONE;
  huart2.Init.Mode         = UART_MODE_TX_RX;
  huart2.Init.HwFlowCtl    = UART_HWCONTROL_NONE;
  huart2.Init.OverSampling = UART_OVERSAMPLING_16;
  if (HAL_UART_Init(&huart2) != HAL_OK) { Error_Handler(); }
}

static void MX_GPIO_Init(void)
{
  GPIO_InitTypeDef GPIO_InitStruct = {0};

  __HAL_RCC_GPIOA_CLK_ENABLE();
  __HAL_RCC_GPIOB_CLK_ENABLE();

  /* LD2 (PA5) */
  GPIO_InitStruct.Pin   = LD2_Pin;
  GPIO_InitStruct.Mode  = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull  = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(GPIOA, &GPIO_InitStruct);

  /* Relay PB3 */
  GPIO_InitStruct.Pin   = RELAY_Pin_Pin;
  GPIO_InitStruct.Mode  = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull  = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(RELAY_Pin_GPIO_Port, &GPIO_InitStruct);
  HAL_GPIO_WritePin(RELAY_Pin_GPIO_Port, RELAY_Pin_Pin, GPIO_PIN_RESET);

  /* DHT11 data (PA1) — khoi tao o OUTPUT HIGH (driver se chuyen mode khi doc) */
  GPIO_InitStruct.Pin   = DHT11_Pin_Pin;
  GPIO_InitStruct.Mode  = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull  = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(DHT11_Pin_GPIO_Port, &GPIO_InitStruct);
  HAL_GPIO_WritePin(DHT11_Pin_GPIO_Port, DHT11_Pin_Pin, GPIO_PIN_SET);

  /* HM10 STATE PB5 (poll input, pulldown) */
  GPIO_InitStruct.Pin  = BLE_STATE_Pin_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_INPUT;
  GPIO_InitStruct.Pull = GPIO_NOPULL;   // thử NOPULL trước; nếu floating đổi sang PULLDOWN
  HAL_GPIO_Init(BLE_STATE_Pin_GPIO_Port, &GPIO_InitStruct);
}

/* ===================== ERROR HANDLER ===================== */
void Error_Handler(void)
{
  __disable_irq();
  while (1) { }
}
#ifdef USE_FULL_ASSERT
void assert_failed(uint8_t *file, uint32_t line)
{
  (void)file; (void)line;
}
#endif
