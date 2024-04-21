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

    ClassParser parser;
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


    // ---INITIALISATION---

    public void initialise(){
        cgen = new ClassGen(original);
        cgen.setMajor(50);
        cgen.setMinor(0);
        cpgen = cgen.getConstantPool();

        valuesStack = new Stack<Number>();
        variables = new HashMap<Integer, Number>();
        loadInstructions = new Stack<InstructionHandle>();


    }

    // ---OPTIMISATION---
    
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
            removeHandle(instructionList, loadInstructions.pop());
            removeHandle(instructionList, loadInstructions.pop());
            handle.setInstruction(createLoadInstruction(valuesStack.peek(), cpgen));
            loadInstructions.push(handle);
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
            removeHandle(instructionList, loadInstructions.pop());
            removeHandle(instructionList, loadInstructions.pop());
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





    // ---HELPERS---

    private boolean getComparisonOutcome(InstructionList instructionList, IfInstruction instruction){
        if (isInstructionComparingWithZero(instruction)) {
            // if its comparing with 0, then only one value is loaded onto the stack (which needs to get removed).
            removeHandle(instructionList, loadInstructions.pop());
            return parseComparisonInstruction(valuesStack.pop(), instruction);
        }
        // usually should be the other way around, but the compiler inverses the instruction (i.e. > becomes <=)
        Number first = valuesStack.pop();
        Number second = valuesStack.pop();
        removeHandle(instructionList, loadInstructions.pop());
        removeHandle(instructionList, loadInstructions.pop());
        return parseComparisonInstruction(first, second, instruction);
    }

    // ********************************************************************************************************************
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
        for (int loopStartBounds = 0; loopStartBounds < loopBounds.size(); loopStartBounds += 2){
            if (handle.getPosition() >= loopBounds.get(loopStartBounds).getPosition() && handle.getPosition() < loopBounds.get(loopStartBounds+1).getPosition()){
                return loopBounds.get(loopStartBounds);
            }
        }
        return null;
    }

    // Method that detects whether the given variable changes during the loop.
    private boolean variableChangesInLoop(InstructionHandle handle, int key){
        InstructionHandle handleInLoop = locateLoopForInstruction(handle);

        while (handleInLoop != null && !(handleInLoop.getInstruction() instanceof GotoInstruction)){
            Instruction instruction = handleInLoop.getInstruction();
            if((instruction instanceof StoreInstruction && ((StoreInstruction)instruction).getIndex() == key) ||
               (instruction instanceof IINC && (((IINC) instruction).getIndex() == key))){
                return true;
            }
            handleInLoop = handleInLoop.getNext();
        }
        return false;
    }

    // Removed instructions from list
    private void removeHandle(InstructionList instructionList, InstructionHandle handle) {
        try {
            instructionList.delete(handle);
        } catch (TargetLostException ignored) { }
    }

    private void removeHandle(InstructionList instructionList, InstructionHandle handle, InstructionHandle targetHandle) {
        try {
            instructionList.delete(handle, targetHandle);
        } catch (TargetLostException ignored){ }
    }


    // checks if the Instruction Loads a constant value.
    private static boolean isLoadConstantValueInstruction(Instruction instruction){
        if(instruction instanceof LDC || instruction instanceof LDC2_W ||
                instruction instanceof SIPUSH || instruction instanceof BIPUSH ||
                instruction instanceof ICONST || instruction instanceof FCONST ||
                instruction instanceof DCONST || instruction instanceof LCONST){
            return true;
        }
        return false;
    }

    // checks if this instruction is an instruction that gets compared with zero.
    private static boolean isInstructionComparingWithZero(Instruction instruction){
        if(instruction instanceof  IFLE || instruction instanceof IFLT || instruction instanceof IFGE ||
                instruction instanceof IFGT || instruction instanceof IFEQ || instruction instanceof IFNE){
            return true;
        }
        return false;
    }

    // Converts Number value into another type. First letter is the starting type, second letter is the target type
    private static Number convertValue(Instruction instruction, Number value) {
        if (instruction instanceof L2I || instruction instanceof F2I || instruction instanceof D2I){
            return value.intValue();
        } else if (instruction instanceof I2L || instruction instanceof F2L || instruction instanceof F2D){
            return value.longValue();
        } else if (instruction instanceof I2F || instruction instanceof L2F || instruction instanceof D2F){
            return value.floatValue();
        } else if (instruction instanceof I2D || instruction instanceof L2D || instruction instanceof F2D){
            return value.doubleValue();
        }
        return -1;
    }

    private static boolean parseComparisonInstruction(Number num, Instruction instruction) {
        switch (instruction.getClass().getSimpleName()) {
            case "IFEQ":
                return num.intValue() == 0;
            case "IFNE":
                return num.intValue() != 0;
            case "IFLE":
                return num.intValue() <= 0;
            case "IFLT":
                return num.intValue() < 0;
            case "IFGE":
                return num.intValue() >= 0;
            case "IFGT":
                return num.intValue() > 0;
            default:
                return false;
        }
    }

    private static boolean parseComparisonInstruction(Number first, Number second, Instruction instruction) {
        switch (instruction.getClass().getSimpleName()) {
            case "IF_ICMPEQ":
                return first.intValue() == second.intValue();
            case "IF_ICMPNE":
                return first.intValue() != second.intValue();
            case "IF_ICMPLE":
                return first.intValue() <= second.intValue();
            case "IF_ICMPLT":
                return first.intValue() < second.intValue();
            case "IF_ICMPGE":
                return first.intValue() >= second.intValue();
            case "IF_ICMPGT":
                return first.intValue() > second.intValue();
            default:
                return false;
        }
    }

    private static Instruction createLoadInstruction(Number value, ConstantPoolGen cpgen) {
        switch (value.getClass().getSimpleName()) {
            case "Double":
                return new LDC2_W(cpgen.addDouble((Double) value)); // pushes double
            case "Integer":
                if ((Integer) value >= -1 && (Integer) value <= 5) {
                    return new ICONST((Integer) value);
                }
                return new LDC(cpgen.addInteger((Integer) value)); // pushes integer.
            case "Long":
                return new LDC2_W(cpgen.addLong((Long) value)); // pushes long
            case "Float":
                return new LDC(cpgen.addFloat((Float) value)); // pushes float.
            default:
                return null;
        }
    }

    // Gets the value that is to be loaded from a load instruction.
    private static Number getLoadConstantValue(Instruction nextInstruction, ConstantPoolGen cpgen) {
        switch (nextInstruction.getClass().getSimpleName()) {
            case "LDC":
                return (Number) ((LDC) nextInstruction).getValue(cpgen);
            case "LDC2_W":
                return ((LDC2_W) nextInstruction).getValue(cpgen);
            case "BIPUSH":
                return ((BIPUSH) nextInstruction).getValue();
            case "SIPUSH":
                return ((SIPUSH) nextInstruction).getValue();
            case "ICONST":
                return ((ICONST) nextInstruction).getValue();
            case "FCONST":
                return ((FCONST) nextInstruction).getValue();
            case "DCONST":
                return ((DCONST) nextInstruction).getValue();
            case "LCONST":
                return ((LCONST) nextInstruction).getValue();
            default:
                return -1;
        }
    }

	// Performs an arithmetic operation using the popping the first 2 values in the stack, and pushing the combined val.
	private static Number performArithmeticOperation(Number second, Number first, Instruction nextInstruction) {
        switch (nextInstruction.getClass().getSimpleName()) {
        case "IADD":
            return first.intValue() + second.intValue();
        case "ISUB":
            return first.intValue() - second.intValue();
        case "IMUL":
            return first.intValue() * second.intValue();
        case "IDIV":
            return first.intValue() / second.intValue();
        case "LADD":
            return first.longValue() + second.longValue();
        case "LSUB":
            return first.longValue() - second.longValue();
        case "LMUL":
            return first.longValue() * second.longValue();
        case "LDIV":
            return first.longValue() / second.longValue();
        case "FADD":
            return first.floatValue() + second.floatValue();
        case "FSUB":
            return first.floatValue() - second.floatValue();
        case "FMUL":
            return first.floatValue() * second.floatValue();
        case "FDIV":
            return first.floatValue() / second.floatValue();
        case "DADD":
            return first.doubleValue() + second.doubleValue();
        case "DSUB":
            return first.doubleValue() - second.doubleValue();
        case "DMUL":
            return first.doubleValue() * second.doubleValue();
        case "DDIV":
            return first.doubleValue() / second.doubleValue();
        default:
            return -1;
        }
	}



    // ---OUTPUT---
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