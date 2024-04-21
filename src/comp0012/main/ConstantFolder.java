package comp0012.main;

import org.apache.bcel.classfile.ClassParser;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.*;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Stack;


public class ConstantFolder {

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


    private boolean deleteElseBranch;
    private boolean blockOperationIfInLoop;


    public ConstantFolder(String classFilePath) {
        try {
            this.parser = new ClassParser(classFilePath);
            this.original = this.parser.parse();
            this.gen = new ClassGen(this.original);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }


    // <------------------------------------------------ Optimisation ------------------------------------------------->

    public void initialise(){
        cgen = new ClassGen(original);
        cgen.setMajor(50);
        cgen.setMinor(0);
        cpgen = cgen.getConstantPool();

        valuesStack = new Stack<Number>();
        variables = new HashMap<Integer, Number>();
        loadInstructions = new Stack<InstructionHandle>();


    }

    
    public void optimize() {
        initialise();

        // Implement your optimization here
        runOptimization();
        this.optimized = cgen.getJavaClass();
    }

    private void runOptimization(){
        int numberOfMethods = cgen.getMethods().length;
        for (int methodPosition = 0; methodPosition < numberOfMethods; methodPosition++ ) {

            Method method = cgen.getMethodAt(methodPosition);
            Code methodCode = method.getCode(); // gets the code inside the method.

            InstructionList instructionList = new InstructionList(methodCode.getCode()); // gets code and makes an list of Instructions.
            MethodGen methodGen = new MethodGen(method.getAccessFlags(), method.getReturnType(), method.getArgumentTypes(),
                    null, method.getName(), cgen.getClassName(), instructionList, cpgen);

            loadLoopBounds(instructionList);
            for (InstructionHandle handle : instructionList.getInstructionHandles()) {
                // Main Optimization (SimpleFolding, ConstantVariableFolding, DynamicVariableFolding).
                handleInstruction(handle, instructionList);
            }

            instructionList.setPositions(true);
            replaceMethodCode(method, methodGen);

            // clearDataContainers();
        }
    }


    // replaces the original method code with the optimized method code.
    private void replaceMethodCode(Method originalMethod, MethodGen methodGen){
        methodGen.setMaxStack();
        methodGen.setMaxLocals();
        Method newMethod = methodGen.getMethod();
        cgen.replaceMethod(originalMethod, newMethod);
    }

    // clears all the data in all the containers.
    private void clearDataContainers() {
        deleteElseBranch = false;
        blockOperationIfInLoop = false;
        loadInstructions.clear();
        valuesStack.clear(); // clears stack for next method.
        variables.clear(); // clears variables for next method.
    }

    // ---HANDLERS---

    // handles the instruction inside of the InstructionHandle by first checking its type then optimising it.
    private void handleInstruction(InstructionHandle handle, InstructionList instructionList){
        Instruction instruction = handle.getInstruction(); 

        if(instruction instanceof GotoInstruction && deleteElseBranch){
            deleteElseBranch = false;
            removeHandle(instructionList, handle, ((GotoInstruction) handle.getInstruction()).getTarget().getPrev());
        } else if(instruction instanceof ConversionInstruction){
            handleConversion(handle, instructionList);
        } else if(instruction instanceof ArithmeticInstruction || instruction instanceof IfInstruction || instruction instanceof LCMP){
            handleArithmeticLogic(instruction, handle, instructionList);
        } else if(instruction instanceof StoreInstruction || instruction instanceof LoadInstruction || isLoadConstantValueInstruction(instruction)){
            handleStoreLoad(instruction, handle, instructionList);
        } else {
            blockOperationIfInLoop = false;
        }
    }

    private void handleStoreLoad(Instruction instruction, InstructionHandle handle, InstructionList instructionList){
        if(instruction instanceof StoreInstruction){
            loadInstructions.pop();
            variables.put(((StoreInstruction) handle.getInstruction()).getIndex(), valuesStack.pop());
        } else if(instruction instanceof LoadInstruction){
            int variableKey = ((LoadInstruction) handle.getInstruction()).getIndex();
            valuesStack.push(variables.get(variableKey));
            blockOperationIfInLoop = blockOperationIfInLoop || variableChangesInLoop(handle, variableKey);
            loadInstructions.push(handle);
        } else if(isLoadConstantValueInstruction(instruction)){
            valuesStack.push(getLoadConstantValue(handle.getInstruction(), cpgen));
            loadInstructions.push(handle);
        }
    }

    private void handleArithmeticLogic(Instruction instruction,InstructionHandle handle, InstructionList instructionList){
        if(blockOperationIfInLoop){
            return;
        } else if(instruction instanceof ArithmeticInstruction){
            valuesStack.push(performArithmeticOperation(valuesStack.pop(), valuesStack.pop(), handle.getInstruction()));
            condenseOperationInstructions(instructionList, handle, valuesStack.peek());
        } else if(instruction instanceof IfInstruction){
            if (getComparisonOutcome(instructionList, (IfInstruction) handle.getInstruction())) {
                deleteElseBranch = true;
                removeHandle(instructionList, handle);
            } else {
                InstructionHandle targetHandle = ((IfInstruction) handle.getInstruction()).getTarget();
                removeHandle(instructionList, handle, targetHandle.getPrev());
            }
        } else if(instruction instanceof LCMP){
            long first = (Long) valuesStack.pop();
            long second = (Long) valuesStack.pop();
            int result = (first > second) ? 1 : (first < second) ? -1 : 0;
            removePreviousTwoLoadInstructions(instructionList);
            valuesStack.push(result);
            handle.setInstruction(createLoadInstruction(result, cpgen));
            loadInstructions.push(handle);
        }
    }

    // Method that converts the value on the top of the stack to another type.
    private void handleConversion(InstructionHandle handle, InstructionList instructionList) {
        if (isLoadConstantValueInstruction(loadInstructions.peek().getInstruction()) || !blockOperationIfInLoop) {
            // if its a constant or if the variable does not change in the loop.
            valuesStack.push(convertValue(handle.getInstruction(), valuesStack.pop()));
            removeHandle(instructionList, loadInstructions.pop()); // remove load instruction
            handle.setInstruction(createLoadInstruction(valuesStack.peek(), cpgen)); // change conversion instruction with load.
            loadInstructions.push(handle); // push new load instruction onto the loadInstruction stack.
        }
    }





    // <=========================================== Auxiliary Methods ================================================>

    private boolean getComparisonOutcome(InstructionList instructionList, IfInstruction instruction){
        if (isInstructionComparingWithZero(instruction)) {
            // if its comparing with 0, then only one value is loaded onto the stack (which needs to get removed).
            removeHandle(instructionList, loadInstructions.pop());
            return parseComparisonInstruction(valuesStack.pop(), instruction);
        }
        // usually should be the other way around, but the compiler inverses the instruction (i.e. > becomes <=)
        Number first = valuesStack.pop();
        Number second = valuesStack.pop();
        removePreviousTwoLoadInstructions(instructionList); // else remove the two values that are being compared.
        return parseComparisonInstruction(first, second, instruction);
    }


    // used when performing an operation such as arithmetic or comparison, to basically reduce 3 instructions to 1.
    private void condenseOperationInstructions(InstructionList instructionList, InstructionHandle handle, Number value) {
        removePreviousTwoLoadInstructions(instructionList); // remove the 2 LOAD Instructions
        switchInstructionToLoadNumber(handle, value); // creates a load instruction that replaces the operation.
    }

    // creates a load instruction using the value argument given, and replaces the instruction in handle with it.
    private void switchInstructionToLoadNumber(InstructionHandle handle, Number value){
        handle.setInstruction(createLoadInstruction(value, cpgen));
        loadInstructions.push(handle);
    }

    //pops the load instructions from the stack, and using that to reference the instructions that need to get deleted.
    //this method is primarily used to remove the load instructions that were used for operations (Arithmetic/Comparison).
    private void removePreviousTwoLoadInstructions(InstructionList instructionList) {
        removeHandle(instructionList, loadInstructions.pop());
        removeHandle(instructionList, loadInstructions.pop());
    }

    //Loads the loop bounds (the first instruction and last instruction of a loop) into an ArrayList.
    private void loadLoopBounds(InstructionList instructionList) {
        loopBounds = new ArrayList<InstructionHandle>();
        for(InstructionHandle handle : instructionList.getInstructionHandles()) {
            if(handle.getInstruction() instanceof GotoInstruction) {
                GotoInstruction instruction = (GotoInstruction) handle.getInstruction(); // casts GoToInstruction
                if (instruction.getTarget().getPosition() < handle.getPosition()){ // if the GoTo leads upwards.
                    loopBounds.add(instruction.getTarget()); // start of loop
                    loopBounds.add(handle); // end of loop (GOTO Instruction)
                }
            }
        }
    }

    // Method that locates the loop that a given instruction belongs to.
    private InstructionHandle locateLoopForInstruction(InstructionHandle handle){
        int instructionPosition = handle.getPosition();
        for (int loopStartBounds = 0; loopStartBounds < loopBounds.size(); loopStartBounds += 2){
            InstructionHandle loopStartInstruction = loopBounds.get(loopStartBounds);
            InstructionHandle loopEndInstruction = loopBounds.get(loopStartBounds+1);

            if (instructionPosition >= loopStartInstruction.getPosition() && instructionPosition < loopEndInstruction.getPosition()){
                return loopStartInstruction;
            }
        }
        return null;
    }

    // Method that detects whether the given variable changes during the loop.
    private boolean variableChangesInLoop(InstructionHandle handle, int key){
        InstructionHandle handleInLoop = locateLoopForInstruction(handle);

        while (handleInLoop != null && !(handleInLoop.getInstruction() instanceof GotoInstruction)){
            Instruction instruction = handleInLoop.getInstruction();
            if (instruction instanceof StoreInstruction) {
                if (((StoreInstruction) instruction).getIndex() == key) return true; // && ((StoreInstruction) instruction).getIndex() == key)
            } else if (instruction instanceof IINC){
                if (((IINC) instruction).getIndex() == key) return true; // && ((StoreInstruction) instruction).getIndex() == key)
            }
            handleInLoop = handleInLoop.getNext();
        }
        return false;
    }

    // Removes an instruction from the instruction list.
    private void removeHandle(InstructionList instructionList, InstructionHandle handle) {
        InstructionHandle nextHandle = handle.getNext(); // used to get the next instruction if its a target.
        try {
            instructionList.delete(handle);
        } catch (TargetLostException e) {
            // raised if targeted by a GOTO or If Instruction etc. Update the targeters with the next Instruction.
            for (InstructionHandle target : e.getTargets()) {
                for (InstructionTargeter targeter : target.getTargeters()) targeter.updateTarget(target, nextHandle);
            }
        }
    }

    // Removes the instructions from two points.
    private void removeHandle(InstructionList instructionList, InstructionHandle handle, InstructionHandle targetHandle) {
        try {
            instructionList.delete(handle, targetHandle);
        } catch (TargetLostException ignored){ }
    }

    // <============================================= Helper Methods ==================================================>

    // checks if the Instruction Loads a constant value.
    private static boolean isLoadConstantValueInstruction(Instruction instruction){
        return (instruction instanceof LDC || instruction instanceof LDC2_W ||
                instruction instanceof SIPUSH || instruction instanceof BIPUSH ||
                instruction instanceof ICONST || instruction instanceof FCONST ||
                instruction instanceof DCONST || instruction instanceof LCONST);
    }

    // checks if this instruction is an instruction that gets compared with zero.
    private static boolean isInstructionComparingWithZero(Instruction instruction){
        return instruction instanceof  IFLE || instruction instanceof IFLT || instruction instanceof IFGE ||
                instruction instanceof IFGT || instruction instanceof IFEQ || instruction instanceof IFNE;
    }

    // Converts Number value into another type. First letter is the starting type, second letter is the target type
    private static Number convertValue(Instruction instruction, Number value) {
        if (instruction instanceof I2D || instruction instanceof L2D || instruction instanceof F2D){
            return value.doubleValue();
        } else if (instruction instanceof I2F || instruction instanceof L2F || instruction instanceof D2F){
            return value.floatValue();
        } else if (instruction instanceof I2L || instruction instanceof D2L || instruction instanceof F2L){
            return value.longValue();
        } else if (instruction instanceof D2I || instruction instanceof F2I || instruction instanceof L2I){
            return value.intValue();
        }
        throw new IllegalStateException("Instruction not recognised");
    }

    // takes in a value and a instruction that compares with 0, and returns the result
	private static boolean parseComparisonInstruction(Number first, Instruction instruction){
        System.out.println("COMPARING WITH 0: " + first);
    	if (instruction instanceof IFLE) return first.intValue() <= 0;
		else if (instruction instanceof IFLT) return first.intValue() < 0;
		else if (instruction instanceof IFGE) return first.intValue() >= 0;
		else if (instruction instanceof IFGT) return first.intValue() > 0;
		else if (instruction instanceof IFEQ) return first.intValue() == 0;
		else if (instruction instanceof IFNE) return first.intValue() != 0;

		throw new IllegalStateException(String.valueOf(instruction)); // if it is None of these objects then error.
	}

    // takes in 2 values and a instruction that compares with 0, and returns the result
    private static boolean parseComparisonInstruction(Number first, Number second, Instruction instruction){
        System.out.println("COMPARING: " + first + " w/ " + second);
        if (instruction instanceof IF_ICMPLE) return first.intValue() <= second.intValue();
        else if (instruction instanceof IF_ICMPLT) return first.intValue() < second.intValue();
        else if (instruction instanceof IF_ICMPGE) return first.intValue() >= second.intValue();
        else if (instruction instanceof IF_ICMPGT) return first.intValue() > second.intValue();
        else if (instruction instanceof IF_ICMPEQ) return first.intValue() == second.intValue();
        else if (instruction instanceof IF_ICMPNE) return first.intValue() != second.intValue();

        throw new IllegalStateException(String.valueOf(instruction)); // if it is None of these objects then error.
    }

    // This method creates a load instruction using the value that was given to it.
	private static Instruction createLoadInstruction(Number value, ConstantPoolGen cpgen){
		if (value instanceof Double){
			return new LDC2_W(cpgen.addDouble((Double) value)); // pushes double
		} else if (value instanceof Integer){
		    int int_value = (Integer) value;
		    if (int_value >= -1 && int_value <= 5) return new ICONST(int_value);
			return new LDC(cpgen.addInteger((Integer) value)); // pushes integer.
		} else if (value instanceof Long){
			return new LDC2_W(cpgen.addLong((Long) value)); // pushes long
		} else if (value instanceof Float){
			return new LDC(cpgen.addFloat((Float) value)); // pushes float.
		}
		throw new IllegalStateException("Illegal Value");
	}

    // Gets the value that is to be loaded from a load instruction.
	private static Number getLoadConstantValue(Instruction nextInstruction, ConstantPoolGen cpgen) {
		if (nextInstruction instanceof LDC) {
		    // LDC loads a integer/float onto the stack.
			return (Number) ((LDC) nextInstruction).getValue(cpgen);
		} else if (nextInstruction instanceof LDC2_W) {
		    // LDC2_W loads a long/double onto the stack.
			return ((LDC2_W) nextInstruction).getValue(cpgen);
		} else if (nextInstruction instanceof BIPUSH) {
		    // BIPUSH loads a byte onto the stack.
			return ((BIPUSH) nextInstruction).getValue();
		} else if (nextInstruction instanceof SIPUSH) {
		    // SIPUSH loads a short onto the stack.
			return ((SIPUSH) nextInstruction).getValue();
		} else if (nextInstruction instanceof ICONST){
		    // ICONST loads an integer constant (value between -1 and 5 inclusive).
			return ((ICONST) nextInstruction).getValue();
		} else if (nextInstruction instanceof FCONST){
		    // FCONST loads a float constant (0.0 or 1.0 or 2.0).
			return ((FCONST) nextInstruction).getValue();
		} else if (nextInstruction instanceof DCONST){
		    // DCONST loads a double constant (0.0 or 1.0).
			return ((DCONST) nextInstruction).getValue();
		} else if (nextInstruction instanceof LCONST){
		    // LCONST loads a long constant (0 or 1).
			return ((LCONST) nextInstruction).getValue();
		}
		return null;
	}

	// Performs an arithmetic operation using the popping the first 2 values in the stack, and pushing the combined val.
	private static Number performArithmeticOperation(Number second, Number first, Instruction nextInstruction) {
		Number combinedValue ;

		// I represents Integer / D represents Double / F represents Float / L represents Long.
        // 4 possible operations (ADD / SUB / MUL / DIV).

		// <------ Integer Operations ------>
		if (nextInstruction instanceof IADD){
			combinedValue = first.intValue() + second.intValue();
		} else if (nextInstruction instanceof ISUB){
			combinedValue = first.intValue() - second.intValue();
		} else if (nextInstruction instanceof IMUL){
			combinedValue = first.intValue() * second.intValue();
		} else if (nextInstruction instanceof IDIV){
			combinedValue = first.intValue() / second.intValue();
		}

		// <------ Double Operations ------>
		else if (nextInstruction instanceof DADD){
			combinedValue = first.doubleValue() + second.doubleValue();
		} else if (nextInstruction instanceof DSUB){
			combinedValue = first.doubleValue() - second.doubleValue();
		} else if (nextInstruction instanceof DMUL){
			combinedValue = first.doubleValue() * second.doubleValue();
		} else if (nextInstruction instanceof DDIV){
			combinedValue = first.doubleValue() / second.doubleValue();
		}

		// <------ Float Operations ------>
		else if (nextInstruction instanceof FADD){
			combinedValue = first.floatValue() + second.floatValue();
		} else if (nextInstruction instanceof FSUB){
			combinedValue = first.floatValue() - second.floatValue();
		} else if (nextInstruction instanceof FMUL){
			combinedValue = first.floatValue() * second.floatValue();
		} else if (nextInstruction instanceof FDIV){
			combinedValue = first.floatValue() / second.floatValue();
		}

		// <------ Long Operations ------>
		else if (nextInstruction instanceof LADD){
			combinedValue = first.longValue() + second.longValue();
		} else if (nextInstruction instanceof LSUB){
			combinedValue = first.longValue() - second.longValue();
		} else if (nextInstruction instanceof LMUL){
			combinedValue = first.longValue() * second.longValue();
		} else if (nextInstruction instanceof LDIV){
			combinedValue = first.longValue() / second.longValue();
		}

		else throw new IllegalStateException("Unrecognised Arithmetic Operation");
        return combinedValue;

	}

	public void write(String optimisedFilePath) {
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