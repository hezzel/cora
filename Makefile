DIST_DIR := ./app/build/distributions
LIB_DIR := ./cora_distribution/lib

all:
	./gradlew clean
	./gradlew build --rerun-tasks --info
	cd $(DIST_DIR) && unzip app.zip
	rm -rf ./cora_distribution/lib
	cp -R $(DIST_DIR)/app/lib $(LIB_DIR)
	rm -rf ./cora_distribution/benchmarks
	cp -R ./benchmarks ./cora_distribution/benchmarks

install:
	mkdir -p ~/.cora
	cp -R ./cora_distribution/bin ~/.cora
	cp -R ./cora_distribution/lib ~/.cora

run_exp_all:
	cd ./cora_distribution && ./run_exp_all.sh
