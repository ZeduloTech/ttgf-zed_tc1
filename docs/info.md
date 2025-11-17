<!---

This file is used to generate your project datasheet. Please fill in the information below and delete any unused
sections.

You can also include images in this folder and reference them in the markdown. Each image must be less than
512 kb in size, and the combined size of all images must be less than 1 MB.
-->

## How it works

See README.md

## How to test

Use e.g TTL-232 to UART interface such that bytes sent via UART to `UART_RX` and observe SPI transfers on
`SPI_SCL`, `SPI_CS`, and `SPI_MOSI`.
Data returned from SPI is echo via `UART_TX`.

## External hardware

None for the board.
