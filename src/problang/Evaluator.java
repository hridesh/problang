package problang;
import static problang.AST.*;
import static problang.Value.*;

import java.util.List;
import java.util.ArrayList;
import java.io.File;
import java.io.IOException;

import problang.Env.*;

public class Evaluator implements Visitor<Value> {
	
	Printer.Formatter ts = new Printer.Formatter();

	Env initEnv = initialEnv(); 
	
	private final java.util.Random _random = new java.util.Random();
	private static final int SAMPLES = 1000; // Monte-Carlo samples per query/expect

	// Thrown by (observe c) when c is false; caught once per sample by query/expect.
	@SuppressWarnings("serial")
	private static class Reject extends RuntimeException {}

	Value valueOf(Program p) {
			try {
				return (Value) p.accept(this, initEnv);
			} catch (Reject r) {
				return new DynamicError("observe failed outside of a query or expect");
			}
	}
	
	@Override
	public Value visit(AddExp e, Env env) {
		List<Exp> operands = e.all();
		double result = 0;
		for(Exp exp: operands) {
			NumVal intermediate = (NumVal) exp.accept(this, env); // Dynamic type-checking
			result += intermediate.v(); //Semantics of AddExp in terms of the target language.
		}
		return new NumVal(result);
	}
	
	@Override
	public Value visit(UnitExp e, Env env) {
		return new UnitVal();
	}

	@Override
	public Value visit(NumExp e, Env env) {
		return new NumVal(e.v());
	}

	@Override
	public Value visit(StrExp e, Env env) {
		return new StringVal(e.v());
	}

	@Override
	public Value visit(BoolExp e, Env env) {
		return new BoolVal(e.v());
	}

	@Override
	public Value visit(DivExp e, Env env) {
		List<Exp> operands = e.all();
		NumVal lVal = (NumVal) operands.get(0).accept(this, env);
		double result = lVal.v(); 
		for(int i=1; i<operands.size(); i++) {
			NumVal rVal = (NumVal) operands.get(i).accept(this, env);
			result = result / rVal.v();
		}
		return new NumVal(result);
	}

	@Override
	public Value visit(MultExp e, Env env) {
		List<Exp> operands = e.all();
		double result = 1;
		for(Exp exp: operands) {
			NumVal intermediate = (NumVal) exp.accept(this, env); // Dynamic type-checking
			result *= intermediate.v(); //Semantics of MultExp.
		}
		return new NumVal(result);
	}

	@Override
	public Value visit(Program p, Env env) {
		try {
			for(DefineDecl d: p.decls())
				d.accept(this, initEnv);
			return (Value) p.e().accept(this, initEnv);
		} catch (ClassCastException e) {
			return new DynamicError(e.getMessage());
		}
	}

	@Override
	public Value visit(SubExp e, Env env) {
		List<Exp> operands = e.all();
		NumVal lVal = (NumVal) operands.get(0).accept(this, env);
		double result = lVal.v();
		for(int i=1; i<operands.size(); i++) {
			NumVal rVal = (NumVal) operands.get(i).accept(this, env);
			result = result - rVal.v();
		}
		return new NumVal(result);
	}

	@Override
	public Value visit(VarExp e, Env env) {
		// Previously, all variables had value 42. New semantics.
		return env.get(e.name());
	}	

	@Override
	public Value visit(LetExp e, Env env) {
		List<String> names = e.names();
		List<Exp> value_exps = e.value_exps();
		List<Value> values = new ArrayList<Value>(value_exps.size());
		
		for(Exp exp : value_exps) 
			values.add((Value)exp.accept(this, env));
		
		Env new_env = env;
		for (int index = 0; index < names.size(); index++)
			new_env = new ExtendEnv(new_env, names.get(index), values.get(index));

		return (Value) e.body().accept(this, new_env);		
	}	
	
	@Override
	public Value visit(DefineDecl e, Env env) {
		String name = e.name();
		Exp value_exp = e.value_exp();
		Value value = (Value) value_exp.accept(this, env);
		((GlobalEnv) initEnv).extend(name, value);
		return new Value.UnitVal();		
	}	

	@Override
	public Value visit(LambdaExp e, Env env) {
		return new Value.FunVal(env, e.formals(), e.body());
	}
	
	@Override
	public Value visit(CallExp e, Env env) {
		Object result = e.operator().accept(this, env);
		if(!(result instanceof Value.FunVal))
			return new Value.DynamicError("Operator not a function in call " +  ts.visit(e, env));
		Value.FunVal operator =  (Value.FunVal) result; //Dynamic checking
		List<Exp> operands = e.operands();

		// Call-by-value semantics
		List<Value> actuals = new ArrayList<Value>(operands.size());
		for(Exp exp : operands) 
			actuals.add((Value)exp.accept(this, env));
		
		List<String> formals = operator.formals();
		if (formals.size()!=actuals.size())
			return new Value.DynamicError("Argument mismatch in call " + ts.visit(e, env));

		Env fun_env = operator.env();
		for (int index = 0; index < formals.size(); index++)
			fun_env = new ExtendEnv(fun_env, formals.get(index), actuals.get(index));
		
		return (Value) operator.body().accept(this, fun_env);
	}
		
	@Override
	public Value visit(IfExp e, Env env) {
		Object result = e.conditional().accept(this, env);
		if(!(result instanceof Value.BoolVal))
			return new Value.DynamicError("Condition not a boolean in expression " +  ts.visit(e, env));
		Value.BoolVal condition =  (Value.BoolVal) result; //Dynamic checking
		
		if(condition.v())
			return (Value) e.then_exp().accept(this, env);
		else return (Value) e.else_exp().accept(this, env);
	}

	@Override
	public Value visit(LessExp e, Env env) { 
		Value.NumVal first = (Value.NumVal) e.first_exp().accept(this, env);
		Value.NumVal second = (Value.NumVal) e.second_exp().accept(this, env);
		return new Value.BoolVal(first.v() < second.v());
	}
	
	@Override
	public Value visit(EqualExp e, Env env) { 
		Value.NumVal first = (Value.NumVal) e.first_exp().accept(this, env);
		Value.NumVal second = (Value.NumVal) e.second_exp().accept(this, env);
		return new Value.BoolVal(first.v() == second.v());
	}

	@Override
	public Value visit(GreaterExp e, Env env) { 
		Value.NumVal first = (Value.NumVal) e.first_exp().accept(this, env);
		Value.NumVal second = (Value.NumVal) e.second_exp().accept(this, env);
		return new Value.BoolVal(first.v() > second.v());
	}
	
	@Override
	public Value visit(CarExp e, Env env) { 
		Value.PairVal pair = (Value.PairVal) e.arg().accept(this, env);
		return pair.fst();
	}
	
	@Override
	public Value visit(CdrExp e, Env env) { 
		Value.PairVal pair = (Value.PairVal) e.arg().accept(this, env);
		return pair.snd();
	}
	
	@Override
	public Value visit(ConsExp e, Env env) { 
		Value first = (Value) e.fst().accept(this, env);
		Value second = (Value) e.snd().accept(this, env);
		return new Value.PairVal(first, second);
	}

	@Override
	public Value visit(ListExp e, Env env) { 
		List<Exp> elemExps = e.elems();
		int length = elemExps.size();
		if(length == 0)
			return new Value.Null();
		
		//Order of evaluation: left to right e.g. (list (+ 3 4) (+ 5 4)) 
		Value[] elems = new Value[length];
		for(int i=0; i<length; i++)
			elems[i] = (Value) elemExps.get(i).accept(this, env);
		
		Value result = new Value.Null();
		for(int i=length-1; i>=0; i--) 
			result = new PairVal(elems[i], result);
		return result;
	}	
	
	@Override
	public Value visit(NullExp e, Env env) {
		Value val = (Value) e.arg().accept(this, env);
		return new BoolVal(val instanceof Value.Null);
	}

	public Value visit(EvalExp e, Env env) {
		StringVal programText = (StringVal) e.code().accept(this, env);
		Program p = _reader.parse(programText.v());
		return (Value) p.accept(this, env);
	}

	public Value visit(ReadExp e, Env env) {
		StringVal fileName = (StringVal) e.file().accept(this, env);
		try {
			String text = Reader.readFile("" + System.getProperty("user.dir") + File.separator + fileName.v());
			return new StringVal(text);
		} catch (IOException ex) {
			return new DynamicError(ex.getMessage());
		}
	}

	@Override
	public Value visit(FlipExp e, Env env) {
		double p = 0.5;
		if (e.prob() != null) {
			Value pv = (Value) e.prob().accept(this, env);
			if (!(pv instanceof NumVal))
				return new DynamicError("flip expects a numeric probability in " + ts.visit(e, env));
			p = ((NumVal) pv).v();
		}
		return new BoolVal(_random.nextDouble() < p);
	}

	@Override
	public Value visit(UniformExp e, Env env) {
		Value lo = (Value) e.lo().accept(this, env);
		Value hi = (Value) e.hi().accept(this, env);
		if (!(lo instanceof NumVal) || !(hi instanceof NumVal))
			return new DynamicError("uniform expects two numbers in " + ts.visit(e, env));
		double a = ((NumVal) lo).v(), b = ((NumVal) hi).v();
		return new NumVal(a + _random.nextDouble() * (b - a));
	}

	@Override
	public Value visit(RandomExp e, Env env) {
		Value n = (Value) e.bound().accept(this, env);
		if (!(n instanceof NumVal))
			return new DynamicError("random expects a numeric bound in " + ts.visit(e, env));
		int bound = (int) ((NumVal) n).v();
		if (bound <= 0)
			return new DynamicError("random expects a positive bound in " + ts.visit(e, env));
		return new NumVal(_random.nextInt(bound));
	}

	@Override
	public Value visit(ObserveExp e, Env env) {
		Value c = (Value) e.cond().accept(this, env);
		if (!(c instanceof BoolVal))
			return new DynamicError("observe expects a boolean condition in " + ts.visit(e, env));
		if (!((BoolVal) c).v()) throw new Reject();
		return new UnitVal();
	}

	@Override
	public Value visit(QueryExp e, Env env) {
		java.util.Map<String,Integer> counts = new java.util.TreeMap<String,Integer>();
		int valid = 0;
		for (int i = 0; i < SAMPLES; i++) {
			try {
				Value v = (Value) e.body().accept(this, env);
				String key = v.tostring();
				counts.put(key, counts.getOrDefault(key, 0) + 1);
				valid++;
			} catch (Reject r) { /* rejected sample: discard */ }
		}
		if (valid == 0)
			return new DynamicError("query: every sample was rejected (is the condition satisfiable?)");
		java.util.Map<String,Double> dist = new java.util.TreeMap<String,Double>();
		for (java.util.Map.Entry<String,Integer> en : counts.entrySet())
			dist.put(en.getKey(), en.getValue() / (double) valid);
		return new DistVal(dist);
	}

	@Override
	public Value visit(ExpectExp e, Env env) {
		double sum = 0; int valid = 0;
		for (int i = 0; i < SAMPLES; i++) {
			try {
				Value v = (Value) e.body().accept(this, env);
				if (v instanceof NumVal) sum += ((NumVal) v).v();
				else if (v instanceof BoolVal) sum += ((BoolVal) v).v() ? 1 : 0;
				else return new DynamicError("expect requires a numeric or boolean body in " + ts.visit(e, env));
				valid++;
			} catch (Reject r) { /* rejected sample: discard */ }
		}
		if (valid == 0)
			return new DynamicError("expect: every sample was rejected (is the condition satisfiable?)");
		return new NumVal(sum / valid);
	}

	private Env initialEnv() {
		GlobalEnv initEnv = new GlobalEnv();
		
		/* Procedure: (read <filename>). Following is same as (define read (lambda (file) (read file))) */
		List<String> formals = new ArrayList<>();
		formals.add("file");
		Exp body = new AST.ReadExp(new VarExp("file"));
		Value.FunVal readFun = new Value.FunVal(initEnv, formals, body);
		initEnv.extend("read", readFun);

		/* Procedure: (require <filename>). Following is same as (define require (lambda (file) (eval (read file)))) */
		formals = new ArrayList<>();
		formals.add("file");
		body = new EvalExp(new AST.ReadExp(new VarExp("file")));
		Value.FunVal requireFun = new Value.FunVal(initEnv, formals, body);
		initEnv.extend("require", requireFun);
		
		/* Add new built-in procedures here */ 
		
		return initEnv;
	}
	
	Reader _reader; 
	public Evaluator(Reader reader) {
		_reader = reader;
	}
}
