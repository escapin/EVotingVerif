### This Makefile does _not_ build the project,
### but produces stub files for KeY.

STUBMAKER_PATH=~/workspace/key-tools/stubmaker
JAVART_PATH=/usr/lib/jvm/java-6-sun/jre/lib

all:	stubs

### Note: some stubs have been modified by hand

stubs:	FILES
	@echo "Producing stubs for verification with KeY..."
	@java -jar $(STUBMAKER_PATH)/stubmaker.jar \
	-expand -list FILES -d stubs \
#	-hideType float -hideType double \
	$(JAVART_PATH)/rt.jar \
	$(JAVART_PATH)/jce.jar \
	> stubmaker.log
# 2>/dev/null
	@cp javaLangObject.stub stubs/java/lang/Object.java
	@cp String.key stubs/java/lang
	@echo "Finished. See stubmaker.log for details."

help:
	@java -jar $(STUBMAKER_PATH)/stubmaker.jar

clean:
	rm -rf stubs stubmaker.log
