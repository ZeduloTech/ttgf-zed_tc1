![](../../workflows/gds/badge.svg) ![](../../workflows/docs/badge.svg) ![](../../workflows/test/badge.svg) ![](../../workflows/fpga/badge.svg)

# Zedulo TestChip1 — UART → SPI Bridge

This testchip integrates UART IP and SPI IP. Incoming bytes from UART are
forwarded to SPI, validating UART/SPI IP integration on silicon.

### Function
- UART IP receives a frame via `UART RX`.
- Bytes are read from RX fifo output into a buffer.
- Each received byte triggers the following:
    - A single-byte SPI transaction, sent to an external SPI slave via
    `MOSI`. SPI uses mode 3.
    - A single-byte SPI transaction, receiving the (external) SPI
    slave's response via `MISO`.
- The SPI slave response is sampled from MISO;
- SPI response returned are written to TX fifo which is echoed out via `UART TX`.

### Pinout
| Pin       | Name      | Dir | Description      |
|-----------|-----------|-----|------------------|
| ui[0]     | UART_RX   | In  | UART receive     |
| ui[1]     | SPI_MISO  | In  | SPI MISO         |
| uo[0]     | UART_TX   | Out | UART transmit    |
| uo[1]     | SPI_SCL   | Out | SPI clock        |
| uo[2]     | SPI_CS    | Out | SPI chip-select  |
| uo[3]     | SPI_MOSI  | Out | SPI MOSI         |
| others    | —         | —   | Unused           |

### Source IP
This design integrates UART and SPI IP derived from the **OpenTitan project**:  
https://github.com/lowRISC/opentitan
