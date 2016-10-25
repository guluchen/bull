import java.util.ArrayList;


public class BooleanFormula {
	public static final int conjunct=0;
	public static final int disjunct=1;
	public static final int literal=2;
	private int t;//
	ArrayList<BooleanFormula> subformulae;
	private int lit;
	BooleanFormula(int t){
		this.t=t;
		if(t!=literal)
			subformulae=new ArrayList<BooleanFormula>();
	}
	
	void add(BooleanFormula sub){
		assert(t!=literal);
		subformulae.add(sub);
	}

	public int getType() {
		return t;
	}

	public int getLit() {
		assert(t==literal);
		return lit;
	}

	public void setLit(int lit) {
		assert(t==literal);
		this.lit = lit;
	}
	
	public void print(){
		switch(t){
		case disjunct:
			if(subformulae.size()==0)
				System.out.print("{ F }");
			else {
				System.out.print("{ ");
				for (BooleanFormula f:subformulae){
					f.print();
					if(subformulae.indexOf(f)!=subformulae.size()-1)
						System.out.print(" | ");
				}
				System.out.print(" }");
			}
			break;
		case conjunct:
			if(subformulae.size()==0)
				System.out.print("{ T }");
			else {
				System.out.print("{ ");
				for (BooleanFormula f:subformulae){
					f.print();
					if(subformulae.indexOf(f)!=subformulae.size()-1)
						System.out.print(" & ");
				}
				System.out.print(" }");
			}
			break;
		case literal:
			System.out.print(getLit());
			break;
			
		}
		
	}
	
	//toCNF

	private void add_clauses(BooleanFormula ret, BooleanFormula f){
		BooleanFormula cur_neg=new BooleanFormula(literal);
		cur_neg.setLit(-next_fresh);

		switch(f.t){
		case conjunct:
			next_fresh++;
			for(int i=0;i<f.subformulae.size();i++){
				BooleanFormula dis=new BooleanFormula(disjunct);
				ret.add(dis);
				dis.add(cur_neg);
				
				if(f.subformulae.get(i).t==literal){
					BooleanFormula temp=new BooleanFormula(literal);
					temp.setLit(f.subformulae.get(i).lit);
					dis.add(temp);
				}else{
					BooleanFormula temp=new BooleanFormula(literal);
					temp.setLit(next_fresh);
					dis.add(temp);
					add_clauses(ret, f.subformulae.get(i));
				}
			}
			break;
		case disjunct:
			BooleanFormula dis=new BooleanFormula(disjunct);
			ret.add(dis);
			dis.add(cur_neg);
			for(int i=0;i<f.subformulae.size();i++){
				if(f.subformulae.get(i).t==literal){
					BooleanFormula temp=new BooleanFormula(literal);
					temp.setLit(f.subformulae.get(i).lit);
					dis.add(temp);
				}else{
					next_fresh++;
					BooleanFormula temp=new BooleanFormula(literal);
					temp.setLit(next_fresh);
					dis.add(temp);
					add_clauses(ret, f.subformulae.get(i));
				}
			}
			break;
		case literal:
			System.out.println("Something wrong");
			System.exit(13);
			break;
		}
	}

	private int next_fresh;

	BooleanFormula to_cnf (int num_var){
		next_fresh=num_var+1;
		BooleanFormula ret=null;
		BooleanFormula cur=new BooleanFormula(literal);
		cur.setLit(next_fresh);
		BooleanFormula cur_neg=new BooleanFormula(literal);
		cur_neg.setLit(-next_fresh);

		switch(t){
		case literal:
			ret=this;
			break;
		case conjunct:
			ret=new BooleanFormula(conjunct);
			ret.add(cur);
			
			for(int i=0;i<subformulae.size();i++){
				BooleanFormula dis=new BooleanFormula(disjunct);
				ret.add(dis);
				dis.add(cur_neg);
				if(subformulae.get(i).t==literal){
					BooleanFormula temp=new BooleanFormula(literal);
					temp.setLit(subformulae.get(i).getLit());
					dis.add(temp);
				}else{
					next_fresh++;
					BooleanFormula temp=new BooleanFormula(literal);
					temp.setLit(next_fresh);
					dis.add(temp);
					add_clauses(ret, subformulae.get(i));
				}
			}
			break;
		case disjunct:
			ret=new BooleanFormula(conjunct);
			ret.add(cur);
			BooleanFormula dis=new BooleanFormula(disjunct);
			ret.add(dis);
			
			for(int i=0;i<subformulae.size();i++){
				BooleanFormula temp=new BooleanFormula(literal);
				if(subformulae.get(i).t==literal){
					temp.setLit(subformulae.get(i).getLit());
					dis.add(temp);
				}else{
					next_fresh++;
					temp.setLit(next_fresh);
					dis.add(temp);
					add_clauses(ret, subformulae.get(i));
				}

			}
			break;
		}
		return ret;
	}
	
	static public BooleanFormula neg(BooleanFormula f){
		BooleanFormula ret=null;
		switch(f.t){
		case literal:
			ret=new BooleanFormula(literal);
			ret.setLit(-f.getLit());
			break;
		case conjunct:
			ret=new BooleanFormula(disjunct);
			for(BooleanFormula sub:f.subformulae){
				BooleanFormula csub=neg(sub);
				ret.add(csub);
			}
			break;
		case disjunct:
			ret=new BooleanFormula(conjunct);
			for(BooleanFormula sub:f.subformulae){
				BooleanFormula csub=neg(sub);
				ret.add(csub);
			}
			break;
		}
		return ret;
	}
	
	static public int num_of_var(BooleanFormula f){
		int n=0, temp;
		switch(f.t){
		case literal:
			return Math.abs(f.getLit());
		default:
			for(BooleanFormula g:f.subformulae){
				temp=num_of_var(g);
				n=n>temp?n:temp;
			}
			break;
		}
		return n;
	}
	
	
}
