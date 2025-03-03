library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;

entity updowncount is
    port (
        rst, clk : in std_logic ;
        up, down : in std_logic ;
        o: out std_logic_vector(0 to 3)
    );
end updowncount;

architecture rtl of updowncount is
    signal count : std_logic_vector(0 to 3) := "0000";
    begin
        process(clk)
        begin
            if (rising_edge(clk)) then
                if (rst = '1') then
                    count <= "0000";
                else
                    if (up = '1' and count <= "1010") then
                        count <= count + "0001";
                    end if;
                    if (down = '1' and count > "0000") then
                        count <= count - "0001";
                    end if;
                end if;
            end if;
        end process;
    o <= count;
end rtl;
