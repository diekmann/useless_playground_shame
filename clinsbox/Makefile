CC		= gcc
CFLAGS		= -ansi -std=c99 -Wall -Wextra -O2 -DDEBUG #-Werror
LIBS		= #-lcurl

# all source files
_SOURCES	= main.c syscall-reporter.c

# the directories used during build
SRCDIR		= src
OBJDIR		= obj
BINDIR		= bin
DOCDIR		= doc

# the output executable
EXECUTABLE	= main.out

# fixing directories and stuff - do not change
_OBJECTS	= $(_SOURCES:.c=.o)
OBJECTS 	= $(patsubst %,$(OBJDIR)/%,$(_OBJECTS))

SOURCES 	= $(patsubst %,$(SRCDIR)/%,$(_SOURCES))


all: clean syscall-names.h $(OBJECTS) $(EXECUTABLE)

$(EXECUTABLE): $(OBJECTS)
	$(CC) -o $(BINDIR)/$(EXECUTABLE) $(CFLAGS) $(OBJECTS) $(LIBS)

$(EXECUTABLE)_static: $(OBJECTS)
	$(CC) -o $(BINDIR)/$(EXECUTABLE) -static-libgcc $(CFLAGS) $(OBJECTS) # `curl-config --static-libs`


$(OBJDIR)/%.o: $(SRCDIR)/%.c
	$(CC) -c -o $@ $(CFLAGS) $<

.PHONY: doc
doc:
	doxygen Doxyfile


syscall-names.h:
	echo "static const char *syscall_names[] = {" > $(SRCDIR)/syscall-names.h ;\
	echo "#include <sys/syscall.h>" | cpp -dM | grep '^#define __NR_' | \
		LC_ALL=C sed -r -n -e 's/^\#define[ \t]+__NR_([a-z0-9_]+)[ \t]+([0-9]+)(.*)/ [\2] = "\1",/p' >> $(SRCDIR)/syscall-names.h ;\
	echo "};" >> $(SRCDIR)/syscall-names.h
	
clean:
	rm -f $(SRCDIR)/syscall-names.h
	rm -f $(OBJDIR)/*.o
	rm -f *.tmp
	rm -f $(BINDIR)/$(EXECUTABLE)
	rm -f $(DOCDIR)/html/*
	rm -f $(DOCDIR)/html || rmdir $(DOCDIR)/html

run: $(EXECUTABLE)
	echo "==== starting ===="
	./$(BINDIR)/$(EXECUTABLE)
	
strace: $(EXECUTABLE)
	echo "==== starting ===="
	strace ./$(BINDIR)/$(EXECUTABLE)

analysis: $(EXECUTABLE)
	ltrace -n 2 -fiS -o ltrace.tmp ./$(BINDIR)/$(EXECUTABLE)
	objdump -D $(BINDIR)/$(EXECUTABLE) > disas.tmp
