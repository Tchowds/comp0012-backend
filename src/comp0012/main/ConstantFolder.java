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
import java.util.Stack;
import java.util.HashMap;
import java.util.List;



public class ConstantFolder {

    private JavaClass optimized;
    private JavaClass original;

    private ClassGen cgen;
    private ConstantPoolGen cpgen;

    private boolean redundElse;
    private boolean inLoop;

    private Stack<Number> values;
    private Stack<InstructionHandle> methodInstructions;
    private HashMap<Integer, Number> variables;
    private List<InstructionHandle> loopsTerminators;

    public ConstantFolder(String classFilePath) {
        try {
            this.original = new ClassParser(classFilePath).parse();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    // ---OPTIMISATION---
    
    public void optimize() {
        cgen = new ClassGen(original);
        cgen.setMajor(50);
        cgen.setMinor(0);
        cpgen = cgen.getConstantPool();

        values = new Stack<Number>();
        variables = new HashMap<Integer, Number>();
        methodInstructions = new Stack<InstructionHandle>();

        // Implement your optimization here
        runOptimization();
        this.optimized = cgen.getJavaClass();
    }

    private void runOptimization(){
        int numberOfMethods = cgen.getMethods().length;
        for (int methodPosition = 0; methodPosition < numberOfMethods; methodPosition++ ) {

            Method method = cgen.getMethodAt(methodPosition);
            Code methodCode = method.getCode();

            InstructionList instructionList = new InstructionList(methodCode.getCode()); // gets code and makes an list of Instructions.
            MethodGen methodGen = new MethodGen(method.getAccessFlags(), method.getReturnType(), method.getArgumentTypes(),
                    null, method.getName(), cgen.getClassName(), instructionList, cpgen);

            findLoopTerminators(instructionList);
            for (InstructionHandle handle : instructionList.getInstructionHandles()) {
                handleInstruction(handle, instructionList);
            }

            instructionList.setPositions(true);
            methodGen.setMaxStack();
            methodGen.setMaxLocals();
            Method newMethod = methodGen.getMethod();
            cgen.replaceMethod(method, newMethod);
        }
    }

    // ---HANDLERS---

    // optimises the instruction inside instructionList
    private void handleInstruction(InstructionHandle handle, InstructionList instructionList){
        Instruction instruction = handle.getInstruction(); 

        if(instruction instanceof GotoInstruction && redundElse){
            redundElse = false;
            delInstruction(instructionList, handle, ((GotoInstruction) handle.getInstruction()).getTarget().getPrev());
        } else if(instruction instanceof ConversionInstruction){
            handleConversion(handle, instructionList);
        } else if(instruction instanceof ArithmeticInstruction || instruction instanceof IfInstruction || instruction instanceof LCMP){
            handleArithmeticLogic(instruction, handle, instructionList);
        } else if(instruction instanceof StoreInstruction || instruction instanceof LoadInstruction || checkLoadConst(instruction)){
            handleStoreLoad(instruction, handle, instructionList);
        } else {
            inLoop = false;
        }
    }

    private void handleStoreLoad(Instruction instruction, InstructionHandle handle, InstructionList instructionList){
        if(instruction instanceof StoreInstruction){
            methodInstructions.pop();
            variables.put(((StoreInstruction) handle.getInstruction()).getIndex(), values.pop());
        } else if(instruction instanceof LoadInstruction){
            int variableKey = ((LoadInstruction) handle.getInstruction()).getIndex();
            values.push(variables.get(variableKey));
            inLoop = inLoop || changeVarInLoop(handle, variableKey);
            methodInstructions.push(handle);
        } else if(checkLoadConst(instruction)){
            values.push(loadConst(handle.getInstruction(), cpgen));
            methodInstructions.push(handle);
        }
    }

    private void handleArithmeticLogic(Instruction instruction,InstructionHandle handle, InstructionList instructionList){
        if(inLoop){
            return;
        } else if(instruction instanceof ArithmeticInstruction){
            values.push(arithmeticEval(values.pop(), values.pop(), handle.getInstruction()));
            delInstruction(instructionList, methodInstructions.pop());
            delInstruction(instructionList, methodInstructions.pop());
            handle.setInstruction(pushConst(values.peek(), cpgen));
            methodInstructions.push(handle);
        } else if(instruction instanceof IfInstruction){
            if (perfCompare(instructionList, (IfInstruction) handle.getInstruction())) {
                redundElse = true;
                delInstruction(instructionList, handle);
            } else {
                InstructionHandle targetHandle = ((IfInstruction) handle.getInstruction()).getTarget();
                delInstruction(instructionList, handle, targetHandle.getPrev());
            }
        } else if(instruction instanceof LCMP){
            long first = (Long) values.pop();
            long second = (Long) values.pop();
            int result = (first > second) ? 1 : (first < second) ? -1 : 0;
            delInstruction(instructionList, methodInstructions.pop());
            delInstruction(instructionList, methodInstructions.pop());
            values.push(result);
            handle.setInstruction(pushConst(result, cpgen));
            methodInstructions.push(handle);
        }
    }

    // Method that converts the value on the top of the stack to another type.
    private void handleConversion(InstructionHandle handle, InstructionList instructionList) {
        if (checkLoadConst(methodInstructions.peek().getInstruction()) || !inLoop) {
            values.push(convertType(handle.getInstruction(), values.pop()));
            delInstruction(instructionList, methodInstructions.pop());
            handle.setInstruction(pushConst(values.peek(), cpgen));
            methodInstructions.push(handle);
        }
    }


    // ---HELPERS---

    // NOTE: Compiler changes from > to <=
    private boolean perfCompare(InstructionList instructionList, IfInstruction instruction){
        if (instruction instanceof  IFLE || instruction instanceof IFLT || instruction instanceof IFGE ||
                instruction instanceof IFGT || instruction instanceof IFEQ || instruction instanceof IFNE) {
            delInstruction(instructionList, methodInstructions.pop());
            return comparisonEval(values.pop(), instruction);
        }
        Number first = values.pop();
        Number second = values.pop();
        delInstruction(instructionList, methodInstructions.pop());
        delInstruction(instructionList, methodInstructions.pop());
        return comparisonEval(first, second, instruction);
    }

    //Loads the loop bounds (the first instruction and last instruction of a loop) into an ArrayList.
    private void findLoopTerminators(InstructionList instructionList) {
        loopsTerminators = new ArrayList<InstructionHandle>();
        for(InstructionHandle handle : instructionList.getInstructionHandles()) {
            if(handle.getInstruction() instanceof GotoInstruction) {
                GotoInstruction instruction = (GotoInstruction) handle.getInstruction();
                if (instruction.getTarget().getPosition() < handle.getPosition()){
                    loopsTerminators.add(instruction.getTarget());
                    loopsTerminators.add(handle);
                }
            }
        }
    }

    // checks if the instruction is in a loop.
    private InstructionHandle whereInLoop(InstructionHandle handle){
        for (int loopStartBounds = 0; loopStartBounds < loopsTerminators.size(); loopStartBounds += 2){
            if (handle.getPosition() >= loopsTerminators.get(loopStartBounds).getPosition() && handle.getPosition() < loopsTerminators.get(loopStartBounds+1).getPosition()){
                return loopsTerminators.get(loopStartBounds);
            }
        }
        return null;
    }

    // does var change in loop
    private boolean changeVarInLoop(InstructionHandle handle, int key){
        InstructionHandle handleInLoop = whereInLoop(handle);

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
    private void delInstruction(InstructionList instructionList, InstructionHandle handle) {
        try {
            instructionList.delete(handle);
        } catch (TargetLostException ignored) { }
    }

    private void delInstruction(InstructionList instructionList, InstructionHandle handle, InstructionHandle targetHandle) {
        try {
            instructionList.delete(handle, targetHandle);
        } catch (TargetLostException ignored){ }
    }


    // checks if the Instruction Loads a constant value.
    private static boolean checkLoadConst(Instruction instruction){
        if(instruction instanceof LDC || instruction instanceof LDC2_W ||
                instruction instanceof SIPUSH || instruction instanceof BIPUSH ||
                instruction instanceof ICONST || instruction instanceof FCONST ||
                instruction instanceof DCONST || instruction instanceof LCONST){
            return true;
        }
        return false;
    }



    // ---CONVERSION---
    private static Number convertType(Instruction instruction, Number num) {
        if (instruction instanceof L2I || instruction instanceof F2I || instruction instanceof D2I){
            return num.intValue();
        } else if (instruction instanceof I2L || instruction instanceof F2L || instruction instanceof F2D){
            return num.longValue();
        } else if (instruction instanceof I2F || instruction instanceof L2F || instruction instanceof D2F){
            return num.floatValue();
        } else if (instruction instanceof I2D || instruction instanceof L2D || instruction instanceof F2D){
            return num.doubleValue();
        }
        return -1;
    }

	private static Number arithmeticEval(Number second, Number first, Instruction nextInstruction) {
        switch (nextInstruction.getClass().getSimpleName()) {
        case "IADD": return first.intValue() + second.intValue();
        case "ISUB":return first.intValue() - second.intValue();
        case "IMUL":return first.intValue() * second.intValue();
        case "IDIV":return first.intValue() / second.intValue();
        case "LADD":return first.longValue() + second.longValue();
        case "LSUB": return first.longValue() - second.longValue();
        case "LMUL":return first.longValue() * second.longValue();
        case "LDIV":return first.longValue() / second.longValue();
        case "FADD":return first.floatValue() + second.floatValue();
        case "FSUB":return first.floatValue() - second.floatValue();
        case "FMUL":return first.floatValue() * second.floatValue();
        case "FDIV":return first.floatValue() / second.floatValue();
        case "DADD":return first.doubleValue() + second.doubleValue();
        case "DSUB": return first.doubleValue() - second.doubleValue();
        case "DMUL":return first.doubleValue() * second.doubleValue();
        case "DDIV":return first.doubleValue() / second.doubleValue();
        default:return -1;
        }
	}
    private static boolean comparisonEval(Number num, Instruction instruction) {
        switch (instruction.getClass().getSimpleName()) {
            case "IFEQ": return num.intValue() == 0;
            case "IFNE": return num.intValue() != 0;
            case "IFLE": return num.intValue() <= 0;
            case "IFLT": return num.intValue() < 0;
            case "IFGE": return num.intValue() >= 0;
            case "IFGT": return num.intValue() > 0;
            default: return false;
        }
    }

    private static boolean comparisonEval(Number num1, Number num2, Instruction instruction) {
        switch (instruction.getClass().getSimpleName()) {
            case "IF_ICMPEQ": return num1.intValue() == num2.intValue();
            case "IF_ICMPNE": return num1.intValue() != num2.intValue();
            case "IF_ICMPLE": return num1.intValue() <= num2.intValue();
            case "IF_ICMPLT": return num1.intValue() < num2.intValue();
            case "IF_ICMPGE": return num1.intValue() >= num2.intValue();
            case "IF_ICMPGT": return num1.intValue() > num2.intValue();
            default: return false;
        }
    }

    private static Number loadConst(Instruction nextInstruction, ConstantPoolGen cpgen) {
        switch (nextInstruction.getClass().getSimpleName()) {
            case "LDC": return (Number) ((LDC) nextInstruction).getValue(cpgen);
            case "LDC2_W": return ((LDC2_W) nextInstruction).getValue(cpgen);
            case "BIPUSH": return ((BIPUSH) nextInstruction).getValue();
            case "SIPUSH": return ((SIPUSH) nextInstruction).getValue();
            case "ICONST": return ((ICONST) nextInstruction).getValue();
            case "FCONST": return ((FCONST) nextInstruction).getValue();
            case "DCONST": return ((DCONST) nextInstruction).getValue();
            case "LCONST": return ((LCONST) nextInstruction).getValue();
            default: return -1;
        }
    }
    private static Instruction pushConst(Number num, ConstantPoolGen cpgen) {
        switch (num.getClass().getSimpleName()) {
            case "Double": return new LDC2_W(cpgen.addDouble((Double) num));
            case "Integer":
                if ((Integer) num >= -1 && (Integer) num <= 5) {
                    return new ICONST((Integer) num);
                }
                return new LDC(cpgen.addInteger((Integer) num)); 
            case "Long": return new LDC2_W(cpgen.addLong((Long) num)); 
            case "Float": return new LDC(cpgen.addFloat((Float) num)); 
            default: return null;
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