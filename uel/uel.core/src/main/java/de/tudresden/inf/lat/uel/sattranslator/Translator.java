package de.tudresden.inf.lat.uel.sattranslator;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Reader;
import java.io.StringReader;
import java.io.StringWriter;
import java.io.Writer;
import java.util.HashMap;
import java.util.Map;
import java.util.StringTokenizer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.tudresden.inf.lat.uel.main.Equation;
import de.tudresden.inf.lat.uel.main.FAtom;
import de.tudresden.inf.lat.uel.main.Goal;
import de.tudresden.inf.lat.uel.main.Literal;

/**
 * 
 * This class performs reduction of goal equations to propositional clauses. The
 * reduction is explained in F. Baader, B. Morawska,
 * "SAT Encoding of Unification in EL", LPAR 2010.
 * 
 * 
 * It has also the methods to translate an output of a sat solver to a unifier.
 * 
 * 
 * @author Barbara Morawska
 * 
 */

public class Translator {

	private Goal goal;

	private Integer identificator = 1;

	/*
	 * Literals are all dis-subsumptions between atoms in the goal the first
	 * hash map maps them to unique numbers.
	 */

	/*
	 * Identifiers are numbers, each number uniquely identifies a literal, i.e.
	 * a subsumption.
	 */
	private HashMap<Integer, Literal> identifiers = new HashMap<Integer, Literal>();

	private HashMap<String, Integer> literals = new HashMap<String, Integer>();

	/**
	 * 
	 * Update is a string of numbers or numbers preceded with "-" encoding the
	 * negation of the computed unifier. This is needed for computation of the
	 * next unifier.
	 * 
	 * 
	 */

	private StringBuilder update = new StringBuilder("");

	public Translator(Goal g) {
		goal = g;
	}

	public Map<String, Integer> getLiterals() {
		return this.literals;
	}

	/**
	 * This method encodes equations into propositional clauses in DIMACS CNF
	 * format, i.e. positive literal is represented by a positive number and a
	 * negative literal is represented by a corresponding negative number. Each
	 * clause is on one line. The end of a clause is marked by 0. Example of a
	 * clause in DIMACS format: 1 -3 0
	 */
	public SatInput getSatInput() {
		StringWriter writer = new StringWriter();
		toCNFWithoutHeader(writer);
		SatInput ret = new SatInput();
		BufferedReader reader = new BufferedReader(new StringReader(
				writer.toString()));
		String line = "";
		while (line != null) {
			try {
				line = reader.readLine();
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
			if (line != null) {
				ret.add(line);
			}
		}
		return ret;
	}

	public StringBuilder getUpdate() {
		return update;
	}

	/*
	 * Method used by UEL to reset string Update values for literals and S(X)
	 * for each X, before the next unifier is computed.
	 */
	public void reset() {

		update = new StringBuilder("");

		for (Integer key : identifiers.keySet()) {

			identifiers.get(key).setValue(false);

		}

		for (String var : goal.getVariables().keySet()) {

			goal.getVariables().get(var).resetS();

		}

	}

	/*
	 * 
	 * Method to create dis-subsumptions and order literals from all pairs of
	 * atoms of the goal
	 */
	private void setLiterals() {

		String first;
		String second;
		Literal literal;

		/*
		 * Literals for dis-subsumptions
		 */

		for (String key1 : goal.getAllAtoms().keySet()) {

			first = key1;

			for (String key2 : goal.getAllAtoms().keySet()) {

				second = key2;
				literal = new Literal(first, second, Literal.SUBSUMPTION);

				literals.put(literal.toString(), identificator);
				identifiers.put(identificator, literal);
				identificator++;
			}
		}

		/*
		 * 
		 * Literals for order on variables
		 */

		for (String key1 : goal.getVariables().keySet()) {

			first = key1;

			for (String key2 : goal.getVariables().keySet()) {

				second = key2;

				literal = new Literal(first, second, Literal.ORDER);

				literals.put(literal.toString(), identificator);
				identifiers.put(identificator, literal);
				identificator++;

			}

		}

	}

	/*
	 * This method is the same as toTBox but it does not overwrite result.
	 * Instead it appends a unifier to the existing file <result>
	 */

	private void toCNFWithoutHeader(Writer infile) {

		PrintWriter out = new PrintWriter(new BufferedWriter(infile));

		setLiterals();

		/*
		 * 
		 * Clauses created in Step 1
		 */

		for (Equation e : goal.getEquations()) {

			/*
			 * Step 1 for constants
			 */

			for (String key1 : goal.getConstants().keySet()) {

				if (!e.getLeft().containsKey(key1)
						&& !e.getRight().containsKey(key1)) {

					/*
					 * constant not in the equation
					 * 
					 * 
					 * 
					 * one side of an equation
					 */

					for (String key3 : e.getRight().keySet()) {
						for (String key2 : e.getLeft().keySet()) {

							Literal lit2 = new Literal(key2, key1,
									Literal.SUBSUMPTION);

							out.print(" -");
							out.print(literals.get(lit2.toString()));
							out.print(" ");

						}

						Literal lit3 = new Literal(key3, key1,
								Literal.SUBSUMPTION);

						out.print(" " + literals.get(lit3.toString()));
						out.println(" 0");

					}

					/*
					 * another side of an equation
					 */

					for (String key2 : e.getLeft().keySet()) {
						for (String key3 : e.getRight().keySet()) {

							Literal lit2 = new Literal(key3, key1,
									Literal.SUBSUMPTION);

							out.print(" -");
							out.print(literals.get(lit2.toString()));
							out.print(" ");

						}

						Literal lit3 = new Literal(key2, key1,
								Literal.SUBSUMPTION);

						out.print(literals.get(lit3.toString()));
						out.println(" 0");

					}

				} else if (!e.getLeft().containsKey(key1)
						&& e.getRight().containsKey(key1)) {

					/*
					 * constant of the right but not on the left
					 */

					for (String key2 : e.getLeft().keySet()) {
						Literal lit4 = new Literal(key2, key1,
								Literal.SUBSUMPTION);

						out.print(" -");
						out.print(literals.get(lit4.toString()));
						out.print(" ");

					}
					out.println(" 0");

				} else if (e.getLeft().containsKey(key1)
						&& !e.getRight().containsKey(key1)) {

					/*
					 * constant on the left but not on the right
					 */

					for (String key3 : e.getRight().keySet()) {
						Literal lit5 = new Literal(key3, key1,
								Literal.SUBSUMPTION);

						out.print(" -");
						out.print(literals.get(lit5.toString()));
						out.print(" ");

					}
					out.println(" 0");

				}
			}

			/*
			 * Step 1 for existential atoms
			 */

			for (String key1 : goal.getEAtoms().keySet()) {

				if (!e.getLeft().containsKey(key1)
						&& !e.getRight().containsKey(key1)) {

					/*
					 * atom not in the equation
					 * 
					 * one side of equation
					 */

					for (String key3 : e.getRight().keySet()) {
						for (String key2 : e.getLeft().keySet()) {

							Literal lit2 = new Literal(key2, key1,
									Literal.SUBSUMPTION);

							out.print(" -");
							out.print(literals.get(lit2.toString()));
							out.print(" ");

						}

						Literal lit3 = new Literal(key3, key1,
								Literal.SUBSUMPTION);

						out.print(literals.get(lit3.toString()));
						out.println(" 0");

					}

					/*
					 * another side of the equation
					 */

					for (String key2 : e.getLeft().keySet()) {
						for (String key3 : e.getRight().keySet()) {

							Literal lit2 = new Literal(key3, key1,
									Literal.SUBSUMPTION);

							out.print(" -");
							out.print(literals.get(lit2.toString()));
							out.print(" ");
						}

						Literal lit3 = new Literal(key2, key1,
								Literal.SUBSUMPTION);

						out.print(literals.get(lit3.toString()));
						out.println(" 0");

					}

				} else if (!e.getLeft().containsKey(key1)
						&& e.getRight().containsKey(key1)) {

					/*
					 * 
					 * existential atom on the right but not on the left side of
					 * an equation
					 */

					for (String key2 : e.getLeft().keySet()) {
						Literal lit4 = new Literal(key2, key1,
								Literal.SUBSUMPTION);

						out.print(" -");
						out.print(literals.get(lit4.toString()));
						out.print(" ");

					}
					out.println(" 0");

					// end of outer if; key1 is not on the left, ask if it
					// is on the right
				} else if (e.getLeft().containsKey(key1)
						&& !e.getRight().containsKey(key1)) {

					/*
					 * 
					 * existential atom on the left but not on the right side of
					 * equation
					 */

					for (String key3 : e.getRight().keySet()) {
						Literal lit5 = new Literal(key3, key1,
								Literal.SUBSUMPTION);

						out.print(" -");
						out.print(literals.get(lit5.toString()));
						out.print(" ");

					}
					out.println(" 0");

				}
			}

		}
		/*
		 * 
		 * Clauses created in Step 2.
		 * 
		 * 
		 * Step 2.1
		 */

		for (String key1 : goal.getConstants().keySet()) {

			for (String key2 : goal.getConstants().keySet()) {

				if (!key2.equals("TOP") && (!key1.equals(key2))) {

					Literal lit = new Literal(key1, key2, Literal.SUBSUMPTION);

					out.print(literals.get(lit.toString()));

					out.println(" 0");

				}

			}

		}

		/*
		 * 
		 * Step 2.2 and Step 2.3
		 */

		for (String key1 : goal.getEAtoms().keySet()) {

			for (String key2 : goal.getEAtoms().keySet()) {

				if (!key1.equals(key2)) {

					String role1 = goal.getEAtoms().get(key1).getName();
					String role2 = goal.getEAtoms().get(key2).getName();

					/*
					 * if roles are not equal, then Step 2.2
					 */

					if (!role1.equals(role2)) {

						Literal lit = new Literal(key1, key2,
								Literal.SUBSUMPTION);

						out.print(literals.get(lit.toString()));

						out.println(" 0");

						/*
						 * if the roles are equal, then clause in Step 2.3
						 */
					} else {

						FAtom child1 = (FAtom) goal.getEAtoms().get(key1)
								.getChild();
						FAtom child2 = (FAtom) goal.getEAtoms().get(key2)
								.getChild();

						String child1name = child1.getName();
						String child2name = child2.getName();

						if (!child1name.equals(child2name)) {

							Literal lit1 = new Literal(child1name, child2name,
									Literal.SUBSUMPTION);

							Literal lit2 = new Literal(key1, key2,
									Literal.SUBSUMPTION);

							out.print(" -");
							out.print(literals.get(lit1.toString()));
							out.print(" ");

							out.print(literals.get(lit2.toString()));
							out.print(" ");

							out.println(" 0");

						}

					}

				}

			}

		}

		/*
		 * 
		 * Step 2.4
		 */

		for (String key1 : goal.getConstants().keySet()) {

			for (String key2 : goal.getEAtoms().keySet()) {

				Literal lit = new Literal(key1, key2, Literal.SUBSUMPTION);

				out.print(literals.get(lit.toString()));

				out.println(" 0");

				if (!key1.equals("TOP")) {

					Literal lit1 = new Literal(key2, key1, Literal.SUBSUMPTION);

					out.print(literals.get(lit1.toString()));

					out.println(" 0");

				}

			}

		}

		/*
		 * Step 3.1
		 * 
		 * Reflexivity for order literals
		 */
		for (String key1 : goal.getVariables().keySet()) {

			Literal lit = new Literal(key1, key1, Literal.ORDER);

			out.print(" -");
			out.print(literals.get(lit.toString()));
			out.print(" ");

			out.println(" 0");

		}// end of clauses in step 2.5

		/*
		 * 
		 * Step 3.1
		 * 
		 * Transitivity for order literals
		 */

		for (String key1 : goal.getVariables().keySet()) {

			for (String key2 : goal.getVariables().keySet()) {

				for (String key3 : goal.getVariables().keySet()) {

					if (!key1.equals(key2) && !key2.equals(key3)) {

						Literal lit1 = new Literal(key1, key2, Literal.ORDER);

						Literal lit2 = new Literal(key2, key3, Literal.ORDER);

						Literal lit3 = new Literal(key1, key3, Literal.ORDER);

						out.print(" -");
						out.print(literals.get(lit1.toString()));
						out.print(" ");

						out.print(" -");
						out.print(literals.get(lit2.toString()));
						out.print(" ");

						out.print(literals.get(lit3.toString()));
						out.print(" ");

						out.println(" 0");

					}

				}

			}

		}

		/*
		 * 
		 * Step 2.5
		 * 
		 * Transitivity of dis-subsumption
		 */

		for (String key1 : goal.getAllAtoms().keySet()) {

			for (String key2 : goal.getAllAtoms().keySet()) {

				for (String key3 : goal.getAllAtoms().keySet()) {

					if (!key1.equals(key2) && !key1.equals(key3)
							&& !key2.equals(key3)) {

						Literal lit1 = new Literal(key1, key2,
								Literal.SUBSUMPTION);

						Literal lit2 = new Literal(key2, key3,
								Literal.SUBSUMPTION);

						Literal lit3 = new Literal(key1, key3,
								Literal.SUBSUMPTION);

						out.print(" -");
						out.print(literals.get(lit3.toString()));
						out.print(" ");

						out.print(literals.get(lit1.toString()));
						out.print(" ");

						out.print(literals.get(lit2.toString()));
						out.print(" ");

						out.println(" 0");

					}

				}
			}
		}

		/*
		 * 
		 * Step 3.2 Disjunction between order literals and dis-subsumption
		 */

		for (String key1 : goal.getEAtoms().keySet()) {

			FAtom eatom = (FAtom) goal.getEAtoms().get(key1);
			FAtom child = (FAtom) eatom.getChild();

			if (child.isVar()) {

				for (String key2 : goal.getVariables().keySet()) {

					Literal lit1 = new Literal(key2, child.getName(),
							Literal.ORDER);

					Literal lit2 = new Literal(key2, key1, Literal.SUBSUMPTION);

					// out.print(" -");
					out.print(literals.get(lit1.toString()));
					out.print(" ");

					out.print(literals.get(lit2.toString()));
					out.print(" ");

					out.println(" 0");

				}

			}

		}

		out.flush();

	}

	/*
	 * This method is the same as toTBox, but does not write a unifier to file
	 * <result>
	 */
	public boolean toTBox(Reader outfile) throws IOException {

		Pattern answer = Pattern.compile("^SAT");
		Matcher manswer;
		String line;
		boolean response = false;

		BufferedReader reader = new BufferedReader(outfile);

		line = reader.readLine();

		manswer = answer.matcher(line);

		if (manswer.find()) {

			response = true;

			Pattern sign = Pattern.compile("^-");
			Matcher msign;

			line = reader.readLine();

			StringTokenizer st = new StringTokenizer(line);

			StringBuilder token;

			while (st.hasMoreTokens()) {

				token = new StringBuilder(st.nextToken());
				msign = sign.matcher(token);

				if (msign.find()) {

					token = token.delete(0, msign.end());

					Integer i = Integer.parseInt(token.toString());

					Literal literal = (Literal) identifiers.get(i);

					literal.setValue(true);

				}

			}

			for (Integer i : identifiers.keySet()) {

				String name1 = identifiers.get(i).getFirst();
				String name2 = identifiers.get(i).getSecond();

				if (identifiers.get(i).getValue()
						&& identifiers.get(i).getKind() == Literal.SUBSUMPTION) {

					if (goal.getVariables().containsKey(name1)) {
						if (goal.getConstants().containsKey(name2)) {

							goal.getVariables()
									.get(name1)
									.addToS((FAtom) goal.getConstants().get(
											name2));

							if (!goal.getVariables().get(name1).isSys()) {
								update.append(i + " ");
							}

						} else if (goal.getEAtoms().containsKey(name2)) {

							goal.getVariables()
									.get(name1)
									.addToS((FAtom) goal.getEAtoms().get(name2));

							if (!goal.getVariables().get(name1).isSys()) {
								update.append(i + " ");
							}
						}
					}

				} else if (identifiers.get(i).getKind() == Literal.SUBSUMPTION) {

					if (goal.getVariables().containsKey(name1)
							&& !goal.getVariables().get(name1).isSys()) {
						if (goal.getConstants().containsKey(name2)) {

							update.append("-" + i + " ");

						} else if (goal.getEAtoms().containsKey(name2)) {

							update.append("-" + i + " ");
						}
					}

				}

			}

			updateWithNegations();
		}

		return response;

	}

	/**
	 * This method reads a file <code>outfile</code> which contains an output
	 * from SAT solver i.e. UNSAT or SAT with the list of true literals. If the
	 * file contains SAT and the list of true literals, the method translates it
	 * to a TBox, which is written to the file <code>result</code> and returns
	 * "true". Otherwise, it writes "NOT UNIFIABLE" to file <code>result</code>
	 * and returns "false".
	 * 
	 * @param outfile
	 * @param result
	 * @throws IOException
	 * @return <code>true</code> if and only if the output of the SAT solver
	 *         contains SAT.
	 */
	public boolean toTBox(Reader outfile, Writer result) throws IOException {

		Pattern answer = Pattern.compile("^SAT");
		Matcher manswer;
		String line;
		boolean response = false;

		BufferedReader reader = new BufferedReader(outfile);

		line = reader.readLine();

		manswer = answer.matcher(line);

		/*
		 * if SAT is in the beginning of the file
		 */
		if (manswer.find()) {

			response = true;

			Pattern sign = Pattern.compile("^-");
			Matcher msign;

			line = reader.readLine();
			StringTokenizer st = new StringTokenizer(line);

			StringBuilder token;

			while (st.hasMoreTokens()) {

				token = new StringBuilder(st.nextToken());
				msign = sign.matcher(token);

				if (msign.find()) {

					token = token.delete(0, msign.end());

					Integer i = Integer.parseInt(token.toString());

					Literal literal = (Literal) identifiers.get(i);

					literal.setValue(true);

				}

			}

			/*
			 * Define S_X for each variable X
			 */

			for (Integer i : identifiers.keySet()) {

				String name1 = identifiers.get(i).getFirst();
				String name2 = identifiers.get(i).getSecond();

				if (identifiers.get(i).getValue()
						&& identifiers.get(i).getKind() == Literal.SUBSUMPTION) {

					if (goal.getVariables().containsKey(name1)) {
						if (goal.getConstants().containsKey(name2)) {

							goal.getVariables()
									.get(name1)
									.addToS((FAtom) goal.getConstants().get(
											name2));

							if (!goal.getVariables().get(name1).isSys()) {
								update.append(i + " ");
							}

						} else if (goal.getEAtoms().containsKey(name2)) {

							goal.getVariables()
									.get(name1)
									.addToS((FAtom) goal.getEAtoms().get(name2));

							if (!goal.getVariables().get(name1).isSys()) {
								update.append(i + " ");
							}
						}
					}

				} else if (identifiers.get(i).getKind() == Literal.SUBSUMPTION) {

					if (goal.getVariables().containsKey(name1)
							&& !goal.getVariables().get(name1).isSys()) {
						if (goal.getConstants().containsKey(name2)) {

							update.append("-" + i + " ");

						} else if (goal.getEAtoms().containsKey(name2)) {

							update.append("-" + i + " ");
						}
					}

				}

			}
			updateWithNegations();

			PrintWriter out = new PrintWriter(new BufferedWriter(result));

			for (String variable : goal.getVariables().keySet()) {

				if (!goal.getVariables().get(variable).isSys()) {
					out.print("(define-concept ");
					out.print(variable + " ");

					goal.getVariables().get(variable).printS(out);
					out.println(" ) ");
				}
			}

			out.flush();

		} else {

			PrintWriter out = new PrintWriter(new BufferedWriter(result));

			out.println("NOT UNIFIABLE");

			out.flush();

		}

		return response;

	}

	public boolean toTBoxB(Reader outfile, Writer result, int numberofsolutions)
			throws IOException {

		Pattern answer = Pattern.compile("^SAT");
		Matcher manswer;
		String line;
		boolean response = false;

		BufferedReader reader = new BufferedReader(outfile);

		line = reader.readLine();

		manswer = answer.matcher(line);

		if (manswer.find()) {

			response = true;

			Pattern sign = Pattern.compile("^-");
			Matcher msign;

			line = reader.readLine();
			StringTokenizer st = new StringTokenizer(line);

			StringBuilder token;

			while (st.hasMoreTokens()) {

				token = new StringBuilder(st.nextToken());
				msign = sign.matcher(token);

				if (msign.find()) {

					token = token.delete(0, msign.end());

					Integer i = Integer.parseInt(token.toString());

					Literal literal = (Literal) identifiers.get(i);

					literal.setValue(true);

				}

			}

			for (Integer i : identifiers.keySet()) {

				String name1 = identifiers.get(i).getFirst();
				String name2 = identifiers.get(i).getSecond();

				if (identifiers.get(i).getValue()
						&& identifiers.get(i).getKind() == Literal.SUBSUMPTION) {

					if (goal.getVariables().containsKey(name1)) {
						if (goal.getConstants().containsKey(name2)) {

							goal.getVariables()
									.get(name1)
									.addToS((FAtom) goal.getConstants().get(
											name2));

							if (!goal.getVariables().get(name1).isSys()) {
								update.append(i + " ");
							}

						} else if (goal.getEAtoms().containsKey(name2)) {

							goal.getVariables()
									.get(name1)
									.addToS((FAtom) goal.getEAtoms().get(name2));

							if (!goal.getVariables().get(name1).isSys()) {
								update.append(i + " ");
							}
						}
					}

				} else if (identifiers.get(i).getKind() == Literal.SUBSUMPTION) {

					if (goal.getVariables().containsKey(name1)
							&& !goal.getVariables().get(name1).isSys()) {
						if (goal.getConstants().containsKey(name2)) {

							update.append("-" + i + " ");

						} else if (goal.getEAtoms().containsKey(name2)) {

							update.append("-" + i + " ");
						}
					}

				}

			}

			updateWithNegations();

			PrintWriter out = new PrintWriter(new BufferedWriter(result));

			for (String variable : goal.getVariables().keySet()) {

				if (!goal.getVariables().get(variable).isSys()) {
					out.print("(define-concept ");
					out.print(variable + " ");

					goal.getVariables().get(variable).printS(out);
					out.println(" ) ");
				}
			}

			out.flush();

		} else {

			PrintWriter out = new PrintWriter(new BufferedWriter(result));

			out.println("NO MORE UNIFIERS");

			out.flush();

		}

		return response;

	}

	private void updateWithNegations() {
		for (FAtom var : goal.getVariables().values()) {
			if (var.getS().isEmpty() && !var.isSys()) {
				for (FAtom atom : goal.getAllAtoms().values()) {
					if (atom.isCons() || atom.isRoot()) {
						Literal lit = new Literal(var.toString(),
								atom.toString(), Literal.SUBSUMPTION);
						int i = literals.get(lit.toString());
						update.append("-" + i + " ");
					}
				}
			}
		}
	}

}
