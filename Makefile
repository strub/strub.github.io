# -*- Makefile -*-

.PHONY: default publish

default:
	@echo "no default action" >&2

publish:
	git commit -m "$$(date)" --amend --date="$$(date)" -a 
	git push -f
