### This Makefile does _not_ build the project,
### but produces stub files for KeY.

STUBMAKER_PATH=~/Programs/key-tools/stubmaker
JAVART_PATH=/usr/lib64/jvm/jre-1.6.0-openjdk/lib

all:	stubs

### Note: some stubs have been modified by hand

stubs:	FILES
	@echo "Producing stubs for verification with KeY..."
	@java -jar $(STUBMAKER_PATH)/stubmaker.jar \
	-hideType float -hideType double \
	-expand -list FILES -d stubs \
	lib/bcprov-jdk16-146.jar \
	$(JAVART_PATH)/rt.jar \
	$(JAVART_PATH)/jce.jar \
	> stubmaker.log
# 2>/dev/null
	@cp javaLangObject.stub stubs/java/lang/Object.java
	@cp String.key stubs/java/lang
	@echo "Finished. See stubmaker.log for details."

clean:
	rm -rf stubs stubmaker.log
