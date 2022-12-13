/**
 * Team Members: 
 *      Katherine Fernandes (kaf245@cornell.edu)
 *      Tiffany Guo (tg382@cornell.edu)
 * Recreation of Red Light Green Light Game from Squid Game
 * 
 * HARDWARE CONNECTIONS
 *   - GPIO 4  ---> PIN_MISO
 *   - GPIO 5  ---> PIN_CS
 *   - GPIO 6  ---> PIN_SCK
 *   - GPIO 7  ---> PIN_MOSI
 *   - GPIO 8  ---> LDAC
 *   - GPIO 10 ---> PWM output for x-axis servo
 *   - GPIO 11 ---> PWM output for y-axis servo
 *   - GPIO 12 ---> UltraSonic Echo (input)
 *   - GPIO 15 ---> UltraSonic Trig (output)
 *   - GPIO 16 ---> Red LEDs
 *   - GPIO 25 ---> Green LED
 *   - GPIO 28 ---> PIR
 * 
 * 
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

#include "pico/stdlib.h"
#include "pico/multicore.h"

#include "hardware/pwm.h"
#include "hardware/irq.h"
#include "hardware/timer.h"

#include "hardware/spi.h"

#include "pt_cornell_rp2040_v1.h"

// Macros for fixed-point arithmetic (faster than floating point)
typedef signed int fix15 ;
#define multfix15(a,b) ((fix15)((((signed long long)(a))*((signed long long)(b)))>>15))
#define float2fix15(a) ((fix15)((a)*32768.0)) 
#define fix2float15(a) ((float)(a)/32768.0)
#define absfix15(a) abs(a) 
#define int2fix15(a) ((fix15)(a << 15))
#define fix2int15(a) ((int)(a >> 15))
#define char2fix15(a) (fix15)(((fix15)(a)) << 15)
#define divfix(a,b) (fix15)( (((signed long long)(a)) << 15) / (b))

// PWM wrap value and clock divide value
// For a CPU rate of 125 MHz, this gives
// a PWM frequency of 50 Hz.
#define WRAPVAL 10000
#define CLKDIV 250.0f

// Variable to hold PWM slice number
uint slice_num ;

// Ultra-sonic sensor
int timeout = 26100;
float soundDuration, distToObjectInCM;
static int temp_cm;
static int count_sonic = 0 ;

// Audio Synthesis - SPI Configurations
//Direct Digital Synthesis (DDS) parameters
#define two32 4294967296.0  // 2^32 (a constant)
#define Fs 40000            // sample rate

// the DDS units - core 0
// Phase accumulator and phase increment. Increment sets output frequency.
volatile unsigned int phase_accum_main_0 ;
volatile unsigned int phase_incr_main_0 ;

// DDS sine table (populated in main())
#define sine_table_size 256
fix15 sin_table[sine_table_size] ;

// Values output to DAC
int DAC_output_0 ;

// Amplitude modulation parameters and variables
fix15 max_amplitude = int2fix15(1) ;    // maximum amplitude
fix15 attack_inc ;                      // rate at which sound ramps up
fix15 decay_inc ;                       // rate at which sound ramps down
fix15 current_amplitude_0 = 0 ;         // current amplitude (modified in ISR)

// Timing parameters for songs (units of interrupts)
// squid game -- red light green light song
#define QUARTER_NOTE 28800
#define EIGHTH_NOTE 14400
#define NOTE_PAUSE 120
#define SONG_PAUSE 200000

#define ATTACK_TIME  150
#define DECAY_TIME   150

#define B_FLAT 466.16 
#define E_FLAT 622.25 
#define D_FLAT 554.37 

float song_frequencies[] = {B_FLAT, E_FLAT, E_FLAT, E_FLAT, D_FLAT, E_FLAT, E_FLAT, B_FLAT, B_FLAT, D_FLAT} ;
int song_durations[] = {EIGHTH_NOTE, EIGHTH_NOTE, QUARTER_NOTE, QUARTER_NOTE, QUARTER_NOTE, EIGHTH_NOTE, EIGHTH_NOTE, EIGHTH_NOTE, EIGHTH_NOTE, QUARTER_NOTE} ;

// winning song
#define WIN_QUARTER_NOTE 20000
#define WIN_EIGHTH_NOTE 10000
#define WIN_NOTE_PAUSE 115

#define G_3 196
#define C_4 261.63
#define E_4 329.63
#define G_4 392
#define C_5 523.25
#define E_5 659.25
#define G_5 783.899

#define A_FLAT_3 207.65
#define E_FLAT_4 311.13
#define A_FLAT_4 415.3
#define E_FLAT_5 622.25
#define A_FLAT_5 830.61

#define B_FLAT_3 233.08
#define D_4      293.66
#define F_4      349.23
#define B_FLAT_4 466.16
#define D_5      587.33
#define F_5      698.46
#define B_FLAT_5 932.33
#define C_6      1046.5

#define B_4 493.88
#define A_4 440

float win_frequencies[] = {B_4, B_4, B_4, B_4, B_4, B_4, E_FLAT_5, B_4, B_4, A_4, G_4, A_4, B_4,
                           B_4, B_4, B_4, B_4, B_4, B_4, B_4, A_4, G_4, A_4, G_4, E_4, E_4 } ;

int win_durations[] = {WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_QUARTER_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_QUARTER_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_QUARTER_NOTE,
                        WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_QUARTER_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_QUARTER_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_EIGHTH_NOTE, WIN_QUARTER_NOTE } ;

// State machine variables
volatile unsigned int STATE_0 = 0 ;
volatile unsigned int count_0 = 0 ;
volatile unsigned int song_index = 0 ;
volatile float rand_speed = 1.0 ; // later randomly generated between 0.5 and 1.5
volatile unsigned int win_count_0 = 0 ;
volatile unsigned int win_index = 0 ;

// SPI data
uint16_t DAC_data_1 ; // output value
uint16_t DAC_data_0 ; // output value

// DAC parameters (see the DAC datasheet)
// A-channel, 1x, active
#define DAC_config_chan_A 0b0011000000000000
// B-channel, 1x, active
#define DAC_config_chan_B 0b1011000000000000

// GPIO Configurations
#define SERVO_X   10
#define SERVO_Y   11

#define ULTRA_TRIG  15
#define ULTRA_ECHO  12

#define GREEN_LED_PIN 25
#define RED_LED_PIN 16

#define PIN_MISO 4
#define PIN_CS   5
#define PIN_SCK  6
#define PIN_MOSI 7
#define LDAC     8
#define SPI_PORT spi0

#define PIR 28

// Movement of head on x-axis
void head_forward() // faces towards the players
{
    pwm_set_chan_level(slice_num, PWM_CHAN_A, 400); 
}

void head_backward() // faces away from the players
{
    pwm_set_chan_level(slice_num, PWM_CHAN_A, 1150);
}

// Movement of head on y-axis
void head_up() // head is upright
{
    pwm_set_chan_level(slice_num, PWM_CHAN_B, 500);
}

void head_fall() // head falls backwards
{
    pwm_set_chan_level(slice_num, PWM_CHAN_B, 1100);
}

// Ultra-sonic sensor functions (from KleistRobotics)
int getPulse(int trigPin, int echoPin)
{
    static int begin_time ;
    static int end_time ;
    gpio_put(trigPin, 0);
    sleep_ms(10);
    gpio_put(trigPin, 1);
    sleep_ms(100);
    gpio_put(trigPin, 0);

    int width = 0;

    while (gpio_get(echoPin) == 0) ;
    begin_time = time_us_32() ; 
    while (gpio_get(echoPin) == 1) 
    {
        width++;
        sleep_us(1);
        if (width > timeout) return 0;
    }
    end_time = time_us_32() ; 
    
    return end_time - begin_time ;
}

int getCm(int trigPin, int echoPin)
{
    int pulseLength = getPulse(trigPin, echoPin);
    return pulseLength / 29 / 2;
}

/**
 * Function to change state to winning state and turn on and off green LED
 * depending on input from ultra sonic sensor
 */
void ultrasonic_sensing() 
{
    for (int i = 0; i < 3; i++){
        temp_cm = getCm(ULTRA_TRIG, ULTRA_ECHO) ;
        if (temp_cm < 30) { // checks if the player is within 30 cm of ultrasonic sensor
            count_sonic += 1 ; // increments counter
        }
    }

    // if there are more than 2 readings of the player being
    // within winning distance the state changes to 3
    if (count_sonic > 2){ 
        gpio_put(GREEN_LED_PIN, 1); // green LED on
        STATE_0 = 3 ; // State changes to 3 (winning song notes)
    } else {
        gpio_put(GREEN_LED_PIN, 0); // green LED off
    }
}

/**
 * Function to turn on and off red LED depending on input from PIR sensor 
 */
void pir_sensing() 
{
    if (gpio_get(PIR)) { // detect movement
        gpio_put(RED_LED_PIN, 1); // red LED on
    } else { // no movement
        gpio_put(RED_LED_PIN, 0); // red LED off
    }
}

/**
 * Squid Game Thread: main thread for right light green light game
 */
static PT_THREAD (protothread_squid_game(struct pt *pt))
{
    PT_BEGIN(pt) ;
    while (1) {
        if (STATE_0 == 2) { // RED LIGHT -- 2
            gpio_put(GREEN_LED_PIN, 0);
            head_up();
            head_forward();
            pir_sensing();
        }
        else if ((STATE_0 == 0) || (STATE_0 == 1)) { // GREEN LIGHT -- 0 or 1
            gpio_put(RED_LED_PIN, 0);
            head_up();
            head_backward();
            ultrasonic_sensing();            
        } else if ((STATE_0 == 3) || (STATE_0 == 4)) { // winnning -- 3 or 4
            gpio_put(GREEN_LED_PIN, 0);
            gpio_put(RED_LED_PIN, 0);
            head_fall();

        }
        
    }
    PT_END(pt) ;
}

// This timer ISR is called on core 0
bool repeating_timer_callback_core_0(struct repeating_timer *t) 
{
    // State 0 - plays notes - GREEN LIGHT
    // State 1 - pauses between notes - GREEN LIGHT
    // State 2 - pause between songs - RED LIGHT
    // State 3 - winning song notes
    // State 4 - pauses between winning song notes

    if (STATE_0 == 0) { // green light song notes
        // Increment sets output frequency for each note in the green light song
        phase_incr_main_0 = (song_frequencies[song_index]*two32)/Fs ;
        // DDS phase and sine table lookup
        phase_accum_main_0 += phase_incr_main_0  ;
        DAC_output_0 = fix2int15(multfix15(current_amplitude_0,
            sin_table[phase_accum_main_0>>24])) + 2048 ;

        // Ramp up amplitude
        if (count_0 < ATTACK_TIME) {
            current_amplitude_0 = (current_amplitude_0 + attack_inc) ;
        }
        // Ramp down amplitude
        else if (count_0 > (song_durations[song_index]*rand_speed) - DECAY_TIME) {
            current_amplitude_0 = (current_amplitude_0 - decay_inc) ;
        }

        // Mask with DAC control bits
        DAC_data_0 = (DAC_config_chan_B | (DAC_output_0 & 0xffff))  ;

        // SPI write (no spinlock b/c of SPI buffer)
        spi_write16_blocking(SPI_PORT, &DAC_data_0, 1) ;

        // Increment the counter
        count_0 += 1 ;

        // State transition to Pauses
        if (count_0 == (song_durations[song_index]*rand_speed)) {
            song_index +=1 ;
            if (song_index < (sizeof(song_durations) / sizeof(song_durations[0]))) {
                STATE_0 = 1 ;
                count_0 = 0 ;
            }
            else {
                STATE_0 = 2 ;
                count_0 = 0 ;
                song_index = 0 ;
            }
        }
    }

    // State transition: green light song note pause
    else if (STATE_0 == 1) {
        count_0 += 1 ;
        if (count_0 == NOTE_PAUSE*rand_speed) {
            current_amplitude_0 = 0 ;
            STATE_0 = 0 ;
            count_0 = 0 ;
        }
    }

    // State transition: red light - pauses between green light song
    else if (STATE_0 == 2) {
        count_0 += 1 ;
        if (count_0 == SONG_PAUSE) {
            current_amplitude_0 = 0 ;
            STATE_0 = 0 ;
            count_0 = 0 ;
            // calculate random song speed between 0.5 and 1.5
            rand_speed = (rand() % 9)*0.1 + 0.5 ;
        }
    }

    else if (STATE_0 == 3) { // winning song notes
        // Increment sets output frequency for each note in the winning song
        phase_incr_main_0 = (win_frequencies[win_index]*two32)/Fs ;
        // DDS phase and sine table lookup
        phase_accum_main_0 += phase_incr_main_0  ;
        DAC_output_0 = fix2int15(multfix15(current_amplitude_0,
            sin_table[phase_accum_main_0>>24])) + 2048 ;

        // Ramp up amplitude
        if (win_count_0 < ATTACK_TIME) {
            current_amplitude_0 = (current_amplitude_0 + attack_inc) ;
        }
        // Ramp down amplitude
        else if (win_count_0 > (win_durations[win_index]) - DECAY_TIME) {
            current_amplitude_0 = (current_amplitude_0 - decay_inc) ;
        }

        // Mask with DAC control bits
        DAC_data_0 = (DAC_config_chan_B | (DAC_output_0 & 0xffff))  ;

        // SPI write (no spinlock b/c of SPI buffer)
        spi_write16_blocking(SPI_PORT, &DAC_data_0, 1) ;

        // Increment the counter
        win_count_0 += 1 ;

        // State transition to winning song pauses
        if (win_count_0 == (win_durations[win_index])) {
            win_index +=1 ;
            if (win_index < (sizeof(win_durations) / sizeof(win_durations[0]))) {
                STATE_0 = 4 ;
                win_count_0 = 0 ;
            }
            else { // after song ends restarts winning song from the beginning
                STATE_0 = 4 ;
                win_count_0 = 0 ;
                win_index = 0 ;
            }
        }
    }

    // State transition: winning song note pause
    else if (STATE_0 == 4) {
        win_count_0 += 1 ;
        if (win_count_0 == WIN_NOTE_PAUSE) {
            current_amplitude_0 = 0 ;
            STATE_0 = 3 ;
            win_count_0 = 0 ;
        }
    }

    return true;
}

int main() 
{
    // Initialize stdio
    stdio_init_all();

    ////////////////////////////////////////////////////////////////////////
    ///////////////////////// PWM CONFIGURATION ////////////////////////////
    ////////////////////////////////////////////////////////////////////////
    // Tell GPIO 10 and GPIO 11 that it is allocated to the PWM
    gpio_set_function(SERVO_X, GPIO_FUNC_PWM);
    gpio_set_dir(SERVO_X, GPIO_OUT) ;
    gpio_set_function(SERVO_Y, GPIO_FUNC_PWM);
    gpio_set_dir(SERVO_Y, GPIO_OUT) ;

    // Find out which PWM slice is connected to GPIO 10 (it's slice 5)
    // GPIO 10 and GPIO 11 are connected to the same PWM slice
    slice_num = pwm_gpio_to_slice_num(SERVO_X);

    // This section configures the period of the PWM signals
    pwm_set_wrap(slice_num, WRAPVAL) ;
    pwm_set_clkdiv(slice_num, CLKDIV) ;

    // This sets duty cycle
    pwm_set_chan_level(slice_num, PWM_CHAN_A, 1150); // X - axis
    pwm_set_chan_level(slice_num, PWM_CHAN_B, 500); // Y - axis

    // Start the channel
    pwm_set_mask_enabled((1u << slice_num));

    ////////////////////////////////////////////////////////////////////////
    ///////////////////////// Ultrasonic Sensor ////////////////////////////
    ////////////////////////////////////////////////////////////////////////
    // Tell GPIO 15 that it is output -- 
    gpio_init(ULTRA_TRIG);
    gpio_set_dir(ULTRA_TRIG, GPIO_OUT) ;
    // Tell GPIO 12 that it is input -- trig
    gpio_init(ULTRA_ECHO);
    gpio_set_dir(ULTRA_ECHO, GPIO_IN) ;

    // Initialize the LED pin
    gpio_init(GREEN_LED_PIN);
    // Configure the LED pin as an output
    gpio_set_dir(GREEN_LED_PIN, GPIO_OUT);
    gpio_put(GREEN_LED_PIN, 0);

    // Initialize the LED pin
    gpio_init(RED_LED_PIN);
    // Configure the LED pin as an output
    gpio_set_dir(RED_LED_PIN, GPIO_OUT);
    gpio_put(RED_LED_PIN, 0);

    ////////////////////////////////////////////////////////////////////////
    ////////////////////////// Audio Sythesis //////////////////////////////
    ////////////////////////////////////////////////////////////////////////
    // initialize random to be based on clock
    srand((unsigned) time_us_32()) ;

    // Initialize SPI channel (channel, baud rate set to 20MHz)
    spi_init(SPI_PORT, 20000000) ;
    // Format (channel, data bits per transfer, polarity, phase, order)
    spi_set_format(SPI_PORT, 16, 0, 0, 0);

    // Map SPI signals to GPIO ports
    gpio_set_function(PIN_MISO, GPIO_FUNC_SPI) ;
    gpio_set_function(PIN_SCK, GPIO_FUNC_SPI) ;
    gpio_set_function(PIN_MOSI, GPIO_FUNC_SPI) ;
    gpio_set_function(PIN_CS, GPIO_FUNC_SPI) ;

    // Map LDAC pin to GPIO port, hold it low (could alternatively tie to GND)
    gpio_init(LDAC) ;
    gpio_set_dir(LDAC, GPIO_OUT) ;
    gpio_put(LDAC, 0) ;

    // set up increments for calculating bow envelope
    attack_inc = divfix(max_amplitude, int2fix15(ATTACK_TIME)) ;
    decay_inc =  divfix(max_amplitude, int2fix15(DECAY_TIME)) ;

    // Build the sine lookup table
    // scaled to produce values between 0 and 4096 (for 12-bit DAC)
    int ii;
    for (ii = 0; ii < sine_table_size; ii++){
         sin_table[ii] = float2fix15(2047*sin((float)ii*6.283/(float)sine_table_size));
    }

    // Create a repeating timer that calls 
    // repeating_timer_callback (defaults core 0)
    struct repeating_timer timer_core_0;

    // Negative delay so means we will call repeating_timer_callback, and call it
    // again 25us (40kHz) later regardless of how long the callback took to execute
    add_repeating_timer_us(-25, 
        repeating_timer_callback_core_0, NULL, &timer_core_0);

    ////////////////////////////////////////////////////////////////////////
    //////////////////////// PIR Motion Sensor /////////////////////////////
    ////////////////////////////////////////////////////////////////////////
    gpio_init(PIR) ;
    gpio_set_dir(PIR, GPIO_IN) ;
    gpio_pull_up(PIR) ;

    ////////////////////////////////////////////////////////////////////////
    ///////////////////////////// ROCK AND ROLL ////////////////////////////
    ////////////////////////////////////////////////////////////////////////
    pt_add_thread(protothread_squid_game) ;

    pt_schedule_start ;

}
