# Set your simulator and compile settings

VCS =  vcs -sverilog -ntb_opts uvm-1.2 -xprop=tmerge +vc -Mupdate -Mdir=build/csrc -line -full64 -kdb -lca -nc \
      -debug_access+all+reverse +vcs+lic+wait +vcs+vcdpluson -timescale=1ns/100ps $(VCS_BAD_WARNINGS) +incdir+. +incdir+$(VCS_UVM_DIR) -top top
#+incdir+<directory>/ for any other folders where source files might be
#use -cm line+branch+cond+fsm for code coverage reporting

VCS_UVM_DIR = /usr/caen/vcs-2023.12-SP2-1/etc/uvm-1.2/

VCS_BAD_WARNINGS = +warn=noTFIPC +warn=noDEBUG_DEP +warn=noENUMASSIGN +warn=noLCA_FEATURES_ENABLED

VCS_COVG = -cm line+branch+assert+cond+fsm

MODULES = rob rs

# Default target
all: simv

.PHONY: build
build:
	mkdir -p build

# Pattern rule to build each module
build/%.simv: $(call get_src_files,$*) | build
	@echo "==> Compiling DUT: $*" 
	$(VCS) $(VCS_COVG) -cm_dir cov_work/$* +incdir+$*/ +incdir+$*/sequences/ -o build/$*.simv $(call get_src_files,$*)
# took out -l $*_compile.log since it seems unnecessary

define get_src_files
$(addprefix $1/, pkg.sv testbench.sv)
endef

$(MODULES): %: build/%.simv
	@echo "==> Running simulation for DUT: $*"
	./build/$*.simv +vcs+coverage+on $(VCS_COVG) +UVM_TESTNAME=$*_test +UVM_VERBOSITY=UVM_LOW -l build/$*_sim.log
	@mkdir -p urgReport/$*
	urg -dir cov_work/$* -report urgReport/$* -metric line+branch+assert+cond+fsm+group
# can use +vcs+lic+wait to wait for vcs licesnes on umich servers if none are free immediately
# use open -a "Google Chrome" urgReport/rs/dashboard.html to open URG report

.PHONY: $(REPORTS) all_report

.PHONY: $(MODULES:%=%_report)

$(MODULES:%=%_report): %_report:
	open -a "Google Chrome" urgReport/$*/dashboard.html

# Rule to run all reports
all_report: $(MODULES:%=%_report)
	@echo "==> All reports generated."

# Clean generated files
clean: clean_exe
	@$(call PRINT_COLOR, 6, note: clean is split into multiple commands you can call separately: $^)

# removes all extra synthesis files and the entire output directory
# use cautiously, this can cause hours of recompiling in project 4
nuke: clean clean_output clean_programs
	@$(call PRINT_COLOR, 6, note: nuke is split into multiple commands you can call separately: $^)

clean_exe:
	@$(call PRINT_COLOR, 3, removing compiled output files)
	rm -rf build/                         			# remove the entire 'build' folder
	rm -rf *simv *.daidir csrc *.key      			# created by simv/syn_simv/vis_simv
	rm -rf vcdplus.vpd vc_hdrs.h          			# created by simv/syn_simv/vis_simv
	rm -rf unifiedInference.log xprop.log 			# created by simv/syn_simv/vis_simv
	rm -rf *.cov cov_report_* cm.log 				# coverage files
	rm -rf cov_work/								# cov work folder
	rm -rf urgReport/								# urg folder
	rm -rf verdi* novas* *fsdb*           			# verdi files
	rm -rf dve* inter.vpd DVEfiles        			# old DVE debugger
	rm -rf tr_db.log                      			# removing extra log file
	rm -rf .fsm.sch.verilog.xml                     # removing extra xml file

clean_top:
	@$(call PRINT_COLOR, 3, removing excess parent directory files)
	rm -rf *simv *.daidir csrc *.key      			# created by simv/syn_simv/vis_simv
	rm -rf vcdplus.vpd vc_hdrs.h          			# created by simv/syn_simv/vis_simv
	rm -rf unifiedInference.log xprop.log 			# created by simv/syn_simv/vis_simv
	rm -rf *.cov cov_report_* cm.log  				# coverage files
	rm -rf verdi* novas* *fsdb*           			# verdi files
	rm -rf dve* inter.vpd DVEfiles        			# old DVE debugger
	rm -rf tr_db.log                      			# removing extra log file
	rm -rf .fsm.sch.verilog.xml                     # removing extra xml file


clean_run_files:
	@$(call PRINT_COLOR, 3, removing per-run outputs)
	rm -rf output/*.out output/*.cpi output/*.wb output/*.log

clean_output:
	@$(call PRINT_COLOR, 1, removing entire output directory)
	rm -rf output/

.PHONY: clean nuke clean_%

PRINT_COLOR = if [ -t 0 ]; then tput setaf $(1) ; fi; echo $(2); if [ -t 0 ]; then tput sgr0; fi