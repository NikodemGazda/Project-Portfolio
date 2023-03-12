#include <stdint.h>
#include <BoardSupport/inc/RGBLedDriver.h>
#include <BoardSupport/inc/I2CDriver.h>
#include "inc/hw_memmap.h"


/* Algorithm to map the 16 bit LED data to 32 bits to send to the LS registers on the LP3943.
*  The algorithm zero extends the 16 bit LED data to 32 bits, then interleaves the 0's with the LED data
*  to give each LED 2 bits to match the format of the LS registers.
*/
static void ConvertData(uint16_t LED_DATA)
{
    REGISTER_LEDS = LED_DATA;
    LEDShiftTemp = (REGISTER_LEDS ^ (REGISTER_LEDS >> 8)) & 0x0000ff00;
    REGISTER_LEDS ^= (LEDShiftTemp ^ (LEDShiftTemp << 8));
    LEDShiftTemp = (REGISTER_LEDS ^ (REGISTER_LEDS >> 4)) & 0x00f000f0;
    REGISTER_LEDS ^= (LEDShiftTemp ^ (LEDShiftTemp << 4));
    LEDShiftTemp = (REGISTER_LEDS ^ (REGISTER_LEDS >> 2)) & 0x0c0c0c0c;
    REGISTER_LEDS ^= (LEDShiftTemp ^ (LEDShiftTemp << 2));
    LEDShiftTemp = (REGISTER_LEDS ^ (REGISTER_LEDS >> 1)) & 0x22222222;
    REGISTER_LEDS ^= (LEDShiftTemp ^ (LEDShiftTemp << 1));

    //shift left for pwm
    //REGISTER_LEDS <<= 1;
}


void LP3943_PWMColorSet(uint32_t color, uint32_t PWM_DATA, uint32_t LED_DATA)
{
    switch (color)
    {
        case BLUE:
            SetSlaveAddress(I2C0_BASE, 0x60);
            break;
        case GREEN:
            SetSlaveAddress(I2C0_BASE, 0x61);
            break;
        case RED:
            SetSlaveAddress(I2C0_BASE, 0x62);
            break;
        default:
            SetSlaveAddress(I2C0_BASE, 0x00);
    }

    // Send out LS register address
    StartTransmission(I2C0_BASE, 0x13);

    // your code
    ContinueTransmission(I2C0_BASE,0x40);

    EndTransmission(I2C0_BASE);
}

void LP3943_LedModeSet(uint32_t color, uint16_t LED_DATA)
{
    switch (color)
    {
        case BLUE:
            SetSlaveAddress(I2C0_BASE, 0x60);
            break;
        case GREEN:
            SetSlaveAddress(I2C0_BASE, 0x61);
            break;
        case RED:
            SetSlaveAddress(I2C0_BASE, 0x62);
            break;
        default:
            SetSlaveAddress(I2C0_BASE, 0x00);
    }

    ConvertData(LED_DATA);

    // Send out LS register address
    StartTransmission(I2C0_BASE, 0x16);

    // your code
    ContinueTransmission(I2C0_BASE,REGISTER_LEDS & 0xff);
    ContinueTransmission(I2C0_BASE,(REGISTER_LEDS>>8) & 0xff);
    ContinueTransmission(I2C0_BASE,(REGISTER_LEDS>>16) & 0xff);
    ContinueTransmission(I2C0_BASE,(REGISTER_LEDS>>24) & 0xff);

    EndTransmission(I2C0_BASE);
}

void TurnOffLEDs(uint_desig color)
{
    LP3943_LedModeSet(color, 0x0000);
}

void InitializeRGBLEDs()
{
    InitializeLEDI2C(I2C0_BASE);
    //LP3943_PWMColorSet(0, 0x0000, 0x0000); //blue
    //LP3943_PWMColorSet(1, 0x0000, 0x0000); //green
    //LP3943_PWMColorSet(2, 0x0000, 0x0000); //red
    TurnOffLEDs(RED);
    TurnOffLEDs(GREEN);
    TurnOffLEDs(BLUE);
}
