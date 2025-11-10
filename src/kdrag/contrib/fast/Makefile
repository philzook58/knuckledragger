all: tests.c fast.c fast.h
	gcc -Wextra -Wall -Werror -fanalyzer -g -fsanitize=address -fsanitize=undefined fast.c tests.c  -l z3 -o test
	./test