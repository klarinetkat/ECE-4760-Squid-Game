add_executable(squid_game)

# must match with executable name and source file names
target_sources(squid_game PRIVATE squid-game.c)

# Add pico_multicore which is required for multicore functionality
target_link_libraries(squid_game pico_stdlib pico_multicore pico_bootsel_via_double_reset hardware_pwm hardware_irq hardware_spi)

# create map/bin/hex file etc.
pico_add_extra_outputs(squid_game)