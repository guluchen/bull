import java.util.HashSet;
import java.util.Scanner;
import java.util.StringTokenizer;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

class Cdnfp{
	private static final int CDNF=0;
	private static final int CDNF_Plus=1;
	private static final int CDNF_PlusPlus=2;
	public boolean isMem(boolean[] bv){
		int varnum=BooleanFormula.num_of_var(tgt);
		BooleanFormula cnf=tgt.to_cnf(varnum);
		HashSet<int[]> clauses=new HashSet<int[]>();
		
		for(BooleanFormula g:cnf.subformulae){
			if(g.getType()==BooleanFormula.disjunct){
				int[] clause=new int[g.subformulae.size()];
				for(int i=0;i<g.subformulae.size();i++){
					BooleanFormula h=g.subformulae.get(i);
					assert(h.getType()==BooleanFormula.literal);
					clause[i]=h.getLit();
				}			
				clauses.add(clause);
			}else{
				int[] clause=new int[1];
				clause[0]=g.getLit();
				clauses.add(clause);
			}
		}
		for(int i=1;i<bv.length;i++){
			int[] clause=new int[1];
			if(bv[i])
				clause[0]=i;
			else
				clause[0]=-i;
			clauses.add(clause);
		}
		if(SAT(varnum,clauses)==null)
			return false;
		else
			return true;
	}
	public boolean isCoMem(boolean[] bv){
		int varnum=BooleanFormula.num_of_var(tgt);
		
		BooleanFormula cnf=BooleanFormula.neg(tgt).to_cnf(varnum);
		HashSet<int[]> clauses=new HashSet<int[]>();
		
		for(BooleanFormula g:cnf.subformulae){
			if(g.getType()==BooleanFormula.disjunct){
				int[] clause=new int[g.subformulae.size()];
				for(int i=0;i<g.subformulae.size();i++){
					BooleanFormula h=g.subformulae.get(i);
					assert(h.getType()==BooleanFormula.literal);
					clause[i]=h.getLit();
				}			
				clauses.add(clause);
			}else{
				int[] clause=new int[1];
				clause[0]=g.getLit();
				clauses.add(clause);
			}
		}
		for(int i=1;i<bv.length;i++){
			int[] clause=new int[1];
			if(bv[i])
				clause[0]=i;
			else
				clause[0]=-i;
			clauses.add(clause);
		}
		if(SAT(varnum,clauses)==null)
			return false;
		else
			return true;
	}

	//null: f equals the target function
	//otherwise: a counterexample in the form of a boolean array
	public boolean[] isEqu(int maxnumvar, BooleanFormula f){
		
		BooleanFormula equ=new BooleanFormula(BooleanFormula.disjunct);
		equ.add(tgt);
		equ.add(BooleanFormula.neg(f));
		int varnum=BooleanFormula.num_of_var(equ);
		
		BooleanFormula cnf=BooleanFormula.neg(equ).to_cnf(varnum);
		HashSet<int[]> clauses=new HashSet<int[]>();

		for(BooleanFormula g:cnf.subformulae){
			if(g.getType()==BooleanFormula.disjunct){
				int[] clause=new int[g.subformulae.size()];
				for(int i=0;i<g.subformulae.size();i++){
					BooleanFormula h=g.subformulae.get(i);
					assert(h.getType()==BooleanFormula.literal);
					clause[i]=h.getLit();
				}			
				clauses.add(clause);
			}else{
				int[] clause=new int[1];
				clause[0]=g.getLit();
				clauses.add(clause);
			}
		}

		int[] result=SAT(varnum,clauses);
		if(result!=null){
			boolean[] bl = new boolean[maxnumvar+1];
			for(int i=0;i<bl.length;i++){
				bl[i]=false;
			}
			for(int j=0;j<result.length;j++){
				if(Math.abs(result[j])<=maxnumvar){
					if(result[j]>0)
						bl[Math.abs(result[j])]=true;
				}
			}
			return bl;
		}else{//check the other direction
			equ=new BooleanFormula(BooleanFormula.disjunct);
			equ.add(f);
			equ.add(BooleanFormula.neg(tgt));
			varnum=BooleanFormula.num_of_var(equ);
						
			
			cnf=BooleanFormula.neg(equ).to_cnf(varnum);
			clauses=new HashSet<int[]>();
			for(BooleanFormula g:cnf.subformulae){
				if(g.getType()==BooleanFormula.disjunct){
					int[] clause=new int[g.subformulae.size()];
					for(int i=0;i<g.subformulae.size();i++){
						BooleanFormula h=g.subformulae.get(i);
						assert(h.getType()==BooleanFormula.literal);
						clause[i]=h.getLit();
					}			
					clauses.add(clause);
				}else{
					int[] clause=new int[1];
					clause[0]=g.getLit();
					clauses.add(clause);
				}
			}
			result=SAT(varnum,clauses);
			if(result!=null){
				boolean[] bl = new boolean[maxnumvar+1];
				for(int i=0;i<bl.length;i++){
					bl[i]=false;
				}
				for(int j=0;j<result.length;j++){
					if(Math.abs(result[j])<=maxnumvar){
						if(result[j]>0)
							bl[Math.abs(result[j])]=true;
					}
				}
				return bl;

			}else{
				return null;
			}
		}
	}

	static{
		System.loadLibrary("Cdnfp");
	}	
	native public BooleanFormula learn(int numVar,int mode);


	static void read_DIMACS(){

		tgt=new BooleanFormula(BooleanFormula.conjunct);
		Scanner scanner = new Scanner(System.in);
		
		do{
			String next=scanner.nextLine();
			if(next.startsWith("exit"))
				break;
			if(!next.startsWith("c")&&!next.startsWith("p")){
				BooleanFormula caluse=new BooleanFormula(BooleanFormula.disjunct);
				StringTokenizer st=new StringTokenizer(next);
				while(st.hasMoreTokens()){
					int i=Integer.parseInt(st.nextToken());
					if(i==0)
						break;
					BooleanFormula lit=new BooleanFormula(BooleanFormula.literal);
					lit.setLit(i);
					caluse.add(lit);
				}
				tgt.add(caluse);
			}
		}while(scanner.hasNext());
	}
	static private BooleanFormula tgt;

	static private void print_help(){
		System.out.println("Usage: ./learn.sh mode < input");
		System.out.println(" mode = 0, using CDNF algorithm");
	        System.out.println(" mode = 1, using CDNF+ algorithm");
	        System.out.println(" mode = 2, using CDNF++ algorithm");
	        System.out.println(" input should contain a CNF formula in DIMACS format\n");
		System.exit(-1);
	}
	public static void main(String[] args) {

		int numVar=1,mode =0;
		if (args.length > 0) {
    			try {
				mode = Integer.parseInt(args[0]);
				read_DIMACS();
				if(mode==CDNF)
					numVar=BooleanFormula.num_of_var(tgt);
				if(mode!=CDNF && mode !=CDNF_Plus && mode != CDNF_PlusPlus)
					print_help();
    			} catch (NumberFormatException e) {
    				print_help();
			}
		}else{
			print_help();
		}					
		BooleanFormula r=new Cdnfp().learn(numVar,mode);
		r.print();
		System.out.println();
        }
	
	int[] SAT(int MAXVAR, HashSet<int[]> clauses){
		ISolver solver = SolverFactory.newDefault();

		solver.newVar(MAXVAR);
		solver.setExpectedNumberOfClauses(clauses.size());
		for (int[] clause:clauses) {
		  try {
			solver.addClause(new VecInt(clause));
			} catch (ContradictionException e) {
				return null;
			} // adapt Array to IVecInt
		}
		
		IProblem problem = solver;
		try {
			if (problem.isSatisfiable()) {
				return problem.findModel();
			} else {
			  return null;
			}
		} catch (TimeoutException e) {
			System.out.print("SAT solver timeout!");
			System.exit(0);
			return null;
		}		
	}	
}
