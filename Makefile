MOD_NAME=github.com/felixlinker/keytrans-verification
EXCLUDE_PKGS="main"

.PHONY: debug
debug:
	java -jar -Xss128m "$(GOBRA_JAR)" \
		--module "$(MOD_NAME)" \
		--recursive \
		--include "." ".verification" \
		--excludePackages "$(EXCLUDE_PKGS)"

.PHONY: verify
verify:
	java -jar -Xss128m "$(GOBRA_JAR)" \
		--module "$(MOD_NAME)" \
		--hyperMode extended \
		--recursive \
		--include "." ".verification" \
		--excludePackages "$(EXCLUDE_PKGS)"

.PHONE: typecheck
typecheck:
	java -jar -Xss128m "$(GOBRA_JAR)" \
		--module "$(MOD_NAME)" \
		--recursive \
		--include "." ".verification" \
		--noVerify