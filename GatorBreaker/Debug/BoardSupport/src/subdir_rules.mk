################################################################################
# Automatically-generated file. Do not edit!
################################################################################

SHELL = cmd.exe

# Each subdirectory must supply rules for building sources it contributes
BoardSupport/src/%.obj: ../BoardSupport/src/%.c $(GEN_OPTS) | $(GEN_FILES) $(GEN_MISC_FILES)
	@echo 'Building file: "$<"'
	@echo 'Invoking: Arm Compiler'
	"C:/ti/ccs1200/ccs/tools/compiler/ti-cgt-arm_20.2.6.LTS/bin/armcl" -mv7M4 --code_state=16 --float_support=FPv4SPD16 -me --opt_for_speed=0 --include_path="C:/Users/Nikodem/OneDrive - University of Florida/fall 22/up2/labs/final" --include_path="C:/Users/Nikodem/OneDrive - University of Florida/fall 22/up2/labs/lab 4/lab/BoardSupport" --include_path="C:/Users/Nikodem/OneDrive - University of Florida/fall 22/up2/labs/lab 4/lab/G8RTOS_Lab2" --include_path="C:/ti/TivaWare_C_Series-2.2.0.295" --include_path="C:/ti/ccs1200/ccs/tools/compiler/ti-cgt-arm_20.2.6.LTS/include" --include_path="C:/ti/ccs1200/ccs/tools/compiler/ti-cgt-arm_20.2.6.LTS/include" --define=ccs="ccs" --define=PART_TM4C123GH6PM -g --c99 --gcc --diag_warning=225 --diag_wrap=off --display_error_number --abi=eabi --preproc_with_compile --preproc_dependency="BoardSupport/src/$(basename $(<F)).d_raw" --obj_directory="BoardSupport/src" $(GEN_OPTS__FLAG) "$<"
	@echo 'Finished building: "$<"'
	@echo ' '


