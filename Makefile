DIST_DIR := ./app/build/distributions
BIN_DIR  := ./cora_distribution/bin
LIB_DIR  := ./cora_distribution/lib

.PHONY: all
all:
	./gradlew clean
	./gradlew build --rerun-tasks --info
	cd $(DIST_DIR) && unzip app.zip
	rm -rf ./cora_distribution/bin
	rm -rf ./cora_distribution/lib
	cp -R $(DIST_DIR)/app/bin $(BIN_DIR)
	cp -R $(DIST_DIR)/app/lib $(LIB_DIR)

define path_question
	$(eval confirm := $(shell read -p "Do you want to automatically add cora to your path? [y/n] > " -r; echo $$REPLY))
	$(if $(filter y Y,$(confirm)),1)
endef

util_confirm_ask = $(strip $(path_question))

add_to_path:
	$(if $(util_confirm_ask), \
		@echo "User said yes", \
		@echo "User said no" \
	)

install:
	@rm -rf ~/.cora
	@mkdir -p ~/.cora
	@mkdir -p ~/.cora/bin
	@cp ./cora_distribution/bin/app ~/.cora/bin/cora
	@cp -R ./cora_distribution/lib ~/.cora
	@echo "Cora was successfully installed at ~/.cora."
	@echo "If you would like to run it from anywhere, please add the following line to your bash profile:"
	@echo 'export PATH="$$HOME/.cora/bin:$$PATH"'
	@echo "For security reasons, this installation script will not change this file for you."

uninstall:
	@echo "Uninstalling cora..."
	rm -rf ~/.cora
	@echo "Done."
	@echo "Note: if you have added ~/.cora to your PATH variable, please remove it manually."

run_exp_all:
	cd ./cora_distribution && ./run_exp_all.sh
