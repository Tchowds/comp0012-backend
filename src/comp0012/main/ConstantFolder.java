package comp0012.main;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;

import org.apache.bcel.util.InstructionFinder;
import org.apache.bcel.classfile.*;
import org.apache.bcel.generic.*;
import java.util.*;

public class ConstantFolder
{
	ClassParser parser = null;
	ClassGen gen = null;
	JavaClass original = null;
	JavaClass optimized = null;

    private ClassGen cgen;
    private ConstantPoolGen cpgen;
    private Stack<Number> valuesStack;
    private Stack<InstructionHandle> loadInstructions;
    private HashMap<Integer, Number> variables;
    private List<InstructionHandle> loopBounds;
    private InstructionFinder finder;

    // these are used for PeepHole Optimization (Detecting dead code).
    private HashMap<Integer, InstructionHandle[]> variableInstructions;
    private HashMap<Integer, Boolean> variableUsed;

    private boolean deleteElseBranch;
    private boolean loopblock;

    private Code methodCode;
    private InstructionList instructionList;
    private MethodGen methodGen;

	public ConstantFolder(String classFilePath)
	{

		try{
			this.parser = new ClassParser(classFilePath);
			this.original = this.parser.parse();
			this.gen = new ClassGen(this.original);
            // could be here initialise

                   // Initializing Class Generator
            this.cgen = new ClassGen(original);
            this.cgen.setMajor(50);  // Set Java class file version to Java 6
            this.cgen.setMinor(0);

            // Constant pool initialization from ClassGen
            this.cpgen = this.cgen.getConstantPool();

            // Initializing stacks for value tracking and load instructions
            this.valuesStack = new Stack<>();
            this.loadInstructions = new Stack<>();

            // Initializing maps for variable tracking and peephole optimization
            this.variables = new HashMap<>();
            this.variableInstructions = new HashMap<>();
            this.variableUsed = new HashMap<>();
            
		} catch(IOException e){
			e.printStackTrace();
		}
	}
	
	public void optimize()
	{
		// Implement your optimization here
        for (Method method : cgen.getMethods()) {
            optimizeMethod(method);
        } //clearData();

		this.optimized = gen.getJavaClass();
	}

    // // clears all the data in all the containers.
    // private void clearData() {
    //     deleteElseBranch = false;
    //     loopblock = false;
    //     loadInstructions.clear();
    //     valuesStack.clear();
    //     variables.clear(); 
    //     variableInstructions.clear();
    //     variableUsed.clear();
    // }

    private void optimizeMethod(Method method) {
        this.methodCode = method.getCode(); // gets the code inside the method.
        this.instructionList = new InstructionList(methodCode.getCode()); // gets code and makes an list of Instructions.
        this.methodGen = new MethodGen(method.getAccessFlags(), method.getReturnType(), method.getArgumentTypes(),
                null, method.getName(), cgen.getClassName(), instructionList, cpgen);

        loopBounds = new ArrayList<InstructionHandle>();
        for (InstructionHandle handle : instructionList.getInstructionHandles()) {
            if (handle.getInstruction() instanceof GotoInstruction) {
                GotoInstruction gotoInstr = (GotoInstruction) handle.getInstruction();
                // Check if the goto instruction points to an earlier instruction, indicating a loop.
                if (gotoInstr.getTarget().getPosition() < handle.getPosition()) {
                    loopBounds.add(gotoInstr.getTarget()); // Start of loop
                    loopBounds.add(handle); // End of loop (GOTO Instruction)
                }
            }
        }

        for (InstructionHandle handle : instructionList.getInstructionHandles()) {
            // Main Optimization (SimpleFolding, ConstantVariableFolding, DynamicVariableFolding).
            handleInstruction(handle, instructionList);
        }

        instructionList.setPositions(true);
        methodGen.setMaxStack();
        methodGen.setMaxLocals();
        Method newMethod = methodGen.getMethod();
        cgen.replaceMethod(method, newMethod);
    }


/////////////////// handling

    /** handles the instruction inside of the InstructionHandle by first checking its type then optimising it.
     *
     * @param handle wrapper that contains the instruction.
     * @param instructionList list of all the instruction, this is required because some changes are made here.
     */
    private void handleInstruction(InstructionHandle handle, InstructionList instructionList){
        Instruction instruction = handle.getInstruction(); // gets the instruction from the instruction handle.
        handleArithmeticAndCompareInstructions(instruction, handle, instructionList);
        handleControlInstructions(instruction, handle, instructionList);
        handleLoadAndConversion(instruction, handle, instructionList);
    }
    
    /**
     * Handles comparison operations, including long and conditional comparisons.
     * @param handle The InstructionHandle containing the comparison instruction.
     * @param instructionList The list of instructions being optimized.
     */
    private void handleArithmeticAndCompareInstructions(Instruction instruction, InstructionHandle handle, InstructionList instructionList) {
        if (loopblock) return; // Exit if operation is blocked within loops.

        if (instruction instanceof ArithmeticInstruction) {
            //System.out.println(instruction.getClass());
            Number second = valuesStack.pop(); // last load is on the top of the stack.
            Number first = valuesStack.pop();
            valuesStack.push(calculateArithmetic(first, second, handle.getInstruction()));
            simplifyToLoadResult(instructionList, handle, valuesStack.peek()); // using peek because it needs to be in stack.
        
        } else if (instruction instanceof LCMP) {
            long first = (Long) valuesStack.pop();
            long second = (Long) valuesStack.pop();
            int result = (first > second) ? 1 : (first < second) ? -1 : 0; // LCMP returns -1, 0, 1 based on comparison.
            deleteTwoLoadInstructions(instructionList); // delete operations leading to the comparison.
            handle.setInstruction(generateLoadInstruction(result, cpgen)); // Replace the current instruction with the result load.
            loadInstructions.push(handle);
            valuesStack.push(result); // Push the result back onto the stack for further operations.
        } else if (instruction instanceof IfInstruction) {
            IfInstruction comparisonInstruction = (IfInstruction) instruction;

            if (getCompareResult(instructionList, comparisonInstruction)) {
                deleteHandle(instructionList, handle); // delete this handle if the comparison is true.
                deleteElseBranch = true; // control the flow based on comparison outcome.
            } else {
                // if outcome is false then delete the comparison and the if branch (all instructions to target).
                InstructionHandle targetHandle = comparisonInstruction.getTarget();
                deleteHandle(instructionList, handle, targetHandle.getPrev());
            }
        }
    }

    // Method that checks whether to delete the Else Branch of an IfInstruction, and deletes it if necessary.
    private void handleControlInstructions(Instruction instruction, InstructionHandle handle, InstructionList instructionList) {
        if (instruction instanceof GotoInstruction) {
            if (deleteElseBranch) {
                deleteElseBranch = false;
                GotoInstruction gotoInstruction = (GotoInstruction) handle.getInstruction();
                InstructionHandle targetHandle = gotoInstruction.getTarget();
                deleteHandle(instructionList, handle, targetHandle.getPrev());
            }
        } else if (instruction instanceof StoreInstruction) {
            Number value = valuesStack.pop(); // Pop the top value from the stack
            loadInstructions.pop(); // delete the corresponding load instruction
            StoreInstruction storeInstruction = (StoreInstruction) handle.getInstruction();
            int variableIndex = storeInstruction.getIndex();
            variables.put(variableIndex, value); // Store the value in the variable map
        }
    }

    /**
     * Handles load and conversion of values based on the type of instruction.
     *
     * @param instruction The current instruction being processed.
     * @param handle The handle to the current instruction.
     * @param instructionList The list of all instructions for possible modification.
     */
    private void handleLoadAndConversion(Instruction instruction, InstructionHandle handle, InstructionList instructionList) {
        if (isConstantLoadInstruction(instruction)) {
            handleLoad(handle);
        } else if (instruction instanceof LoadInstruction) {
            handleVariableLoad(handle);
        } else if (instruction instanceof ConversionInstruction) {
            handleConvert(handle, instructionList);
        } else {
            loopblock = false;
        }
    }

    /**
     * Loads a constant value onto the stack and records the load instruction.
     *
     * @param handle The instruction handle associated with the load operation.
     */
    private void handleLoad(InstructionHandle handle) {
        Number constantValue = getConstantValue(handle.getInstruction(), cpgen);
        valuesStack.push(constantValue);
        loadInstructions.push(handle);
    }

    /**
     * Handles the loading of a variable's value onto the stack and checks for variable changes in loops.
     *
     * @param handle The instruction handle associated with the variable load.
     */
    private void handleVariableLoad(InstructionHandle handle) {
        LoadInstruction loadInstruction = (LoadInstruction) handle.getInstruction();
        int variableIndex = loadInstruction.getIndex();
        Number variableValue = variables.getOrDefault(variableIndex, 0); // Provide a default value if not found
        valuesStack.push(variableValue);
        loadInstructions.push(handle);
        loopblock |= variableChangesInLoop(handle, variableIndex);
    }

    /**
     * Converts the top value of the stack according to the conversion instruction,
     * and replaces the conversion instruction with a direct load of the converted value.
     *
     * @param handle The instruction handle for the conversion.
     * @param instructionList The list of all instructions for modification.
     */
    private void handleConvert(InstructionHandle handle, InstructionList instructionList) {
        if (!valuesStack.isEmpty() && (isConstantLoadInstruction(loadInstructions.peek().getInstruction()) || !loopblock)) {
            Number topValue = valuesStack.pop();
            Number convertedValue = convertNumberBasedOnInstruction(handle.getInstruction(), topValue);
            valuesStack.push(convertedValue);
            InstructionHandle previousLoad = loadInstructions.pop();
            deleteHandle(instructionList, previousLoad);
            handle.setInstruction(generateLoadInstruction(convertedValue, cpgen));
            loadInstructions.push(handle);
        }
    }
///////////////////////////////// helper
    /**
     * Simplifies a sequence of operations ending in a calculation into a single load instruction that directly loads the result.
     *
     * @param instructionList The list of instructions in the method, used to delete the unneeded load statements.
     * @param handle The instruction handle where the operation instruction will be replaced.
     * @param value The resultant value from the operation, that requires a Load Instruction.
     */
    private void simplifyToLoadResult(InstructionList instructionList, InstructionHandle handle, Number value) {
        deleteTwoLoadInstructions(instructionList);  // delete the two LOAD Instructions that precede the operation.
        // Replace the operation instruction with a LOAD instruction that loads the resultant value.
        Instruction newLoadInstruction = generateLoadInstruction(value, cpgen);
        handle.setInstruction(newLoadInstruction);
        loadInstructions.push(handle);  // Optionally track the new load instruction if needed for further operations.
    }

    /**
     * Evaluates the outcome of a comparison instruction and updates the instruction list accordingly.
     * @param instructionList The list of bytecode instructions.
     * @param instruction The IfInstruction to evaluate.
     * @return The result of the comparison based on the values currently on the stack.
     */
    private boolean getCompareResult(InstructionList instructionList, IfInstruction instruction) {
        boolean result;

        // Determine if the comparison is against zero, which only involves one value from the stack.
        if (isZeroComparisonInstruction(instruction)) {
            // Pop the single value from the stack used in the comparison.
            Number value = valuesStack.pop();
            deleteHandle(instructionList, loadInstructions.pop());
            result = evaluateComparison(value, instruction);
        } else {
            // For non-zero comparisons, two values are involved.
            Number second = valuesStack.pop();
            Number first = valuesStack.pop();
            deleteTwoLoadInstructions(instructionList); // delete the instructions that loaded both values.
            result = evaluateComparison(first, second, instruction);
        }

        return result;
    }

    /**
     * Determines if a variable changes within the loop that a given instruction belongs to.
     *
     * @param handle The InstructionHandle containing the instruction to check.
     * @param key The index of the variable to track.
     * @return true if the variable changes within the loop; false otherwise.
     */
    private boolean variableChangesInLoop(InstructionHandle handle, int key) {
        InstructionHandle handleInLoop = instInLoop(handle);

        while (handleInLoop != null) {
            Instruction instruction = handleInLoop.getInstruction();
            if (instruction instanceof StoreInstruction && ((StoreInstruction) instruction).getIndex() == key) {
                return true;
            } else if (instruction instanceof IINC && ((IINC) instruction).getIndex() == key) {
                return true;
            }
            if (instruction instanceof GotoInstruction) {
                break;
            }
            handleInLoop = handleInLoop.getNext();
        }
        return false;
    }

    /**
     * Locates the loop that a given instruction belongs to.
     *
     * This method searches through known loop bounds to determine if the given instruction
     * handle is within any defined loops, returning the starting instruction handle of the loop.
     *
     * @param handle InstructionHandle containing the target instruction.
     * @return InstructionHandle representing the start of the loop, or null if not found within any loop.
     */
    private InstructionHandle instInLoop(InstructionHandle handle) {
        int instructionPosition = handle.getPosition();
        // Iterate over pairs of instruction handles that define the start and end of loops
        for (int i = 0; i < loopBounds.size(); i += 2) {
            InstructionHandle loopStart = loopBounds.get(i);
            InstructionHandle loopEnd = loopBounds.get(i + 1);

            if (instructionPosition >= loopStart.getPosition() &&
                instructionPosition < loopEnd.getPosition()) {
                return loopStart;
            }
        }
        return null;
    }


    //pops the load instructions from the stack, and using that to reference the instructions that need to get deleted.
    //this method is primarily used to delete the load instructions that were used for operations (Arithmetic/Comparison).
    /**
     * Deletes the last two load instructions used in operations like Arithmetic/Comparison.
     * @param instructionList The list of bytecode instructions.
     */
    public void deleteTwoLoadInstructions(InstructionList instructionList) {
        deleteHandle(instructionList, loadInstructions.pop());
        deleteHandle(instructionList, loadInstructions.pop());
    }
    /**
     * delete  an instruction from the instruction list safely, updating targeters if necessary.
     * @param instructionList The list of bytecode instructions.
     * @param handle The instruction handle to be delete .
     */
    private void deleteHandle(InstructionList instructionList, InstructionHandle handle) {
        try {
            instructionList.delete(handle);
        } catch (TargetLostException e) {
           handleTargetLostException(handle, e);
        }
    }

    /** delete  the instructions from two points.
     *
     * @param instructionList the list of instructions.
     * @param handle starting point instruction (where to start deleting from)
     * @param targetHandle end point instruction (where to stop deleting)
     */
    private void deleteHandle(InstructionList instructionList, InstructionHandle handle, InstructionHandle targetHandle) {
        try {
            instructionList.delete(handle, targetHandle);
        } catch (TargetLostException ignored){ }
    }

    /**
     * Handles the `TargetLostException` when an instruction with targeters is delete .
     * @param originalHandle The instruction handle that was delete  and caused the exception.
     * @param e The caught TargetLostException.
     */
    private void handleTargetLostException(InstructionHandle originalHandle, TargetLostException e) {
        InstructionHandle nextHandle = originalHandle.getNext(); // Fetch the next handle to update targeters.
        for (InstructionHandle lostTarget : e.getTargets()) {
            for (InstructionTargeter targeter : lostTarget.getTargeters()) {
                targeter.updateTarget(lostTarget, nextHandle);
            }
        }
    }

/////////////////basic
    /**
     * Evaluates a comparison against zero based on the provided instruction.
     * @param value The value to compare with zero.
     * @param instruction The comparison instruction.
     * @return The result of the comparison.
     */
    private static boolean evaluateComparison(Number value, Instruction instruction) {
        switch (instruction.getClass().getSimpleName()) {
            case "IFLE": return value.intValue() <= 0;
            case "IFLT": return value.intValue() < 0;
            case "IFGE": return value.intValue() >= 0;
            case "IFGT": return value.intValue() > 0;
            case "IFEQ": return value.intValue() == 0;
            case "IFNE": return value.intValue() != 0;
            default: throw new IllegalStateException("Unexpected instruction: " + instruction);
        }
    }

    /**
     * Evaluates a comparison between two values based on the provided instruction.
     * @param first The first value.
     * @param second The second value.
     * @param instruction The comparison instruction.
     * @return The result of the comparison.
     */
    private static boolean evaluateComparison(Number first, Number second, Instruction instruction) {
        switch (instruction.getClass().getSimpleName()) {
            case "IF_ICMPLE": return first.intValue() <= second.intValue();
            case "IF_ICMPLT": return first.intValue() < second.intValue();
            case "IF_ICMPGE": return first.intValue() >= second.intValue();
            case "IF_ICMPGT": return first.intValue() > second.intValue();
            case "IF_ICMPEQ": return first.intValue() == second.intValue();
            case "IF_ICMPNE": return first.intValue() != second.intValue();
            default: throw new IllegalStateException("Unexpected instruction: " + instruction);
        }
    }

    /**
     * Converts a Number to another type based on the provided instruction.
     * @param instruction The conversion instruction.
     * @param value The value to convert.
     * @return The converted value as a Number.
     */
    private static Number convertNumberBasedOnInstruction(Instruction instruction, Number value) {
        if (instruction instanceof I2D || instruction instanceof L2D || instruction instanceof F2D) {
            return value.doubleValue();
        } else if (instruction instanceof I2F || instruction instanceof L2F || instruction instanceof D2F) {
            return value.floatValue();
        } else if (instruction instanceof I2L || instruction instanceof D2L || instruction instanceof F2L) {
            return value.longValue();
        } else if (instruction instanceof D2I || instruction instanceof F2I || instruction instanceof L2I) {
            return value.intValue();
        }
        throw new IllegalStateException("Unsupported conversion instruction: " + instruction);
    }

    /**
     * Checks if the instruction compares a value with zero.
     * @param instruction The instruction to check.
     * @return true if it compares a value with zero, false otherwise.
     */
    private static boolean isZeroComparisonInstruction(Instruction instruction) {
        return instruction instanceof IFLE || instruction instanceof IFLT ||
            instruction instanceof IFGE || instruction instanceof IFGT ||
            instruction instanceof IFEQ || instruction instanceof IFNE;
    }

    /**
     * Determines if the given instruction is a constant load instruction.
     * @param instruction The instruction to check.
     * @return true if it is a constant load instruction, false otherwise.
     */
    private static boolean isConstantLoadInstruction(Instruction instruction) {
        return instruction instanceof LDC || instruction instanceof LDC2_W ||
            instruction instanceof SIPUSH || instruction instanceof BIPUSH ||
            instruction instanceof ICONST || instruction instanceof FCONST ||
            instruction instanceof DCONST || instruction instanceof LCONST;
    }


    /**
     * Retrieves the value loaded by a specific load instruction.
     *
     * @param instruction The load instruction.
     * @param cpgen The constant pool generator used for looking up constant values.
     * @return The Number value loaded by the instruction.
     */
    private static Number getConstantValue(Instruction instruction, ConstantPoolGen cpgen) {
        if (instruction instanceof LDC) {
            // LDC loads an int or float constant from the constant pool.
            return (Number) ((LDC) instruction).getValue(cpgen);
        } else if (instruction instanceof LDC2_W) {
            // LDC2_W loads a long or double constant from the constant pool.
            return ((LDC2_W) instruction).getValue(cpgen);
        } else if (instruction instanceof BIPUSH) {
            // BIPUSH instruction, loading a byte.
            return ((BIPUSH) instruction).getValue();
        } else if (instruction instanceof SIPUSH) {
            // SIPUSH instruction, loading a short.
            return ((SIPUSH) instruction).getValue();
        } else if (instruction instanceof ICONST || instruction instanceof FCONST ||
                   instruction instanceof DCONST || instruction instanceof LCONST) {
            // Handle direct push instructions for constants.
            if (instruction instanceof ConstantPushInstruction) {
                return ((ConstantPushInstruction) instruction).getValue();
            }
        }
        return null;
    }
    

    /**
     * Generates an instruction to load a given number value onto the stack.
     *
     * @param value A Number object that represents a value.
     * @param cpgen The constant pool generator used for adding constants.
     * @return The appropriate load instruction for the given value.
     */
    private static Instruction generateLoadInstruction(Number value, ConstantPoolGen cpgen) {
        if (value instanceof Integer) {
            int intValue = (Integer) value;
            if (intValue >= -1 && intValue <= 5) {
                return new ICONST(intValue);
            }
            return new LDC(cpgen.addInteger(intValue));
        } else if (value instanceof Long) {
            return new LDC2_W(cpgen.addLong((Long) value));
        } else if (value instanceof Float) {
            return new LDC(cpgen.addFloat((Float) value));
        } else if (value instanceof Double) {
            return new LDC2_W(cpgen.addDouble((Double) value));
        }
        throw new IllegalArgumentException("Unsupported value type: " + value.getClass().getSimpleName());
    }

    /**
     * Performs an arithmetic operation based on the specified instruction, using two provided values.
     *
     * @param first The first operand.
     * @param second The second operand.
     * @param instruction The instruction that specifies the arithmetic operation.
     * @return The result of the arithmetic operation as a Number.
     */
    private static Number calculateArithmetic(Number first, Number second, Instruction nextInstruction) {
        if (nextInstruction instanceof IADD || nextInstruction instanceof ISUB ||
            nextInstruction instanceof IMUL || nextInstruction instanceof IDIV) {
            int f = first.intValue();
            int s = second.intValue();
            if (nextInstruction instanceof IADD) return f + s;
            if (nextInstruction instanceof ISUB) return f - s;
            if (nextInstruction instanceof IMUL) return f * s;
            if (nextInstruction instanceof IDIV) return f / s;
        }
        else if (nextInstruction instanceof DADD || nextInstruction instanceof DSUB ||
                 nextInstruction instanceof DMUL || nextInstruction instanceof DDIV) {
            double f = first.doubleValue();
            double s = second.doubleValue();
            if (nextInstruction instanceof DADD) return f + s;
            if (nextInstruction instanceof DSUB) return f - s;
            if (nextInstruction instanceof DMUL) return f * s;
            if (nextInstruction instanceof DDIV) return f / s;
        }
        else if (nextInstruction instanceof FADD || nextInstruction instanceof FSUB ||
                 nextInstruction instanceof FMUL || nextInstruction instanceof FDIV) {
            float f = first.floatValue();
            float s = second.floatValue();
            if (nextInstruction instanceof FADD) return f + s;
            if (nextInstruction instanceof FSUB) return f - s;
            if (nextInstruction instanceof FMUL) return f * s;
            if (nextInstruction instanceof FDIV) return f / s;
        }
        else if (nextInstruction instanceof LADD || nextInstruction instanceof LSUB ||
                 nextInstruction instanceof LMUL || nextInstruction instanceof LDIV) {
            long f = first.longValue();
            long s = second.longValue();
            if (nextInstruction instanceof LADD) return f + s;
            if (nextInstruction instanceof LSUB) return f - s;
            if (nextInstruction instanceof LMUL) return f * s;
            if (nextInstruction instanceof LDIV) return f / s;
        }
        else {
            throw new IllegalStateException("Unrecognized Arithmetic Operation");
        }
        throw new IllegalStateException("Unrecognized Type for Operation");
    }
    
    

	
	public void write(String optimisedFilePath)
	{
		this.optimize();

		try {
			FileOutputStream out = new FileOutputStream(new File(optimisedFilePath));
			this.optimized.dump(out);
		} catch (FileNotFoundException e) {
			// Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// Auto-generated catch block
			e.printStackTrace();
		}
	}
}