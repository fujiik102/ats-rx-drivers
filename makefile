
rx_pin_test: rx_pin_test.dats Pin.prooven Bit.prooven rx_pin_emulate.o rx_pin_test.o
	patscc -o $@ rx_pin_test.dats rx_pin_emulate.o rx_pin_test.o

.PHONY : typecheck
typecheck: rx_pin_test.dats Pin.prooven Bit.prooven
	patsopt -tc -d $<

clean:
	-rm *.o
	-rm *_dats.c
	-rm *.prooven

%_dats.c: %.dats %.sats
	patsopt -o $^.c -d $^

%.prooven: %.dats %.sats
	patsopt -tc -d $<
	echo "prooven at `date`"	 > $@

