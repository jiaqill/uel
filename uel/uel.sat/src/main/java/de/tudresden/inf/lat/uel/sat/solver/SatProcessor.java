package de.tudresden.inf.lat.uel.sat.solver;

import java.io.IOException;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Logger;

import de.tudresden.inf.lat.uel.sat.type.AuxiliaryLiteral;
import de.tudresden.inf.lat.uel.sat.type.DissubsumptionLiteral;
import de.tudresden.inf.lat.uel.sat.type.Literal;
import de.tudresden.inf.lat.uel.sat.type.OrderLiteral;
import de.tudresden.inf.lat.uel.sat.type.SubsumptionLiteral;
import de.tudresden.inf.lat.uel.type.api.Atom;
import de.tudresden.inf.lat.uel.type.api.Equation;
import de.tudresden.inf.lat.uel.type.api.IndexedSet;
import de.tudresden.inf.lat.uel.type.api.SmallEquation;
import de.tudresden.inf.lat.uel.type.api.UelInput;
import de.tudresden.inf.lat.uel.type.api.UelOutput;
import de.tudresden.inf.lat.uel.type.api.UelProcessor;
import de.tudresden.inf.lat.uel.type.impl.ConceptName;
import de.tudresden.inf.lat.uel.type.impl.EquationImpl;
import de.tudresden.inf.lat.uel.type.impl.ExistentialRestriction;
import de.tudresden.inf.lat.uel.type.impl.ExtendedUelInput;
import de.tudresden.inf.lat.uel.type.impl.IndexedSetImpl;
import de.tudresden.inf.lat.uel.type.impl.UelOutputImpl;

/**
 * This class performs reduction of goal equations to propositional clauses. The
 * reduction is explained in F. Baader, B. Morawska,
 * "SAT Encoding of Unification in EL", LPAR 2010.
 * 
 * This algorithm is explained below:
 * 
 * <div> Given a flat <i>EL</i>-unification problem &Gamma;, the set C(&Gamma;)
 * consists of the following clauses:
 * 
 * <ul>
 * <li>(1) Translation of the equations of &Gamma;. For every equation
 * A<sub>1</sub> &#8851; &hellip; &#8851; A<sub>m</sub> &equiv;<sup>?</sup>
 * B<sub>1</sub> &#8851; &hellip; &#8851; B<sub>n</sub> of &Gamma;, we create
 * the following Horn clauses, which express that any atom that occurs as a
 * top-level conjunct on one side of an equivalence must subsume a top-level
 * conjunct on the other side:
 * 
 * <ul>
 * <li>1. For every non-variable atom C &isin; {A<sub>1</sub>, &hellip; ,
 * A<sub>m</sub>}:<br />
 * [B<sub>1</sub> &#8930; C] &and; &hellip; &and; [B<sub>n</sub> &#8930; C]
 * &rarr;</li>
 * 
 * <li>2. For every non-variable atom C &isin; {B<sub>1</sub>, &hellip; ,
 * B<sub>n</sub>}:<br />
 * [A<sub>1</sub> &#8930; C] &and; &hellip; &and; [A<sub>m</sub> &#8930; C]
 * &rarr;</li>
 * 
 * <li>3. For every non-variable atom C of &Gamma; s.t. C &notin;
 * {A<sub>1</sub>, &hellip; A<sub>m</sub>, B<sub>1</sub>, &hellip;,
 * B<sub>n</sub>}:<br />
 * [A<sub>1</sub> &#8930; C] &and; &hellip; &and; [A<sub>m</sub> &#8930; C]
 * &rarr; [B<sub>j</sub> &#8930; C] for j = 1, &hellip;, n<br />
 * [B<sub>1</sub> &#8930; C] &and; &hellip; &and; [B<sub>n</sub> &#8930; C]
 * &rarr; [A<sub>i</sub> &#8930; C] for i = 1, &hellip;, m</li>
 * </ul>
 * </li>
 * 
 * <li>(2) Translation of the relevant properties of subsumption in <i>EL</i>.
 * 
 * <ul>
 * <li>1. For every pair of distinct concept constants A, B occurring in
 * &Gamma;, we say that A cannot be subsumed by B:<br />
 * &rarr; [A &#8930; B]</li>
 * 
 * <li>2. For every pair of distinct role names r, s and atoms
 * &exist;r<i>.</i>A, &exist;s<i>.</i>B of &Gamma;, we say that
 * &exist;r<i>.</i>A cannot be subsumed by &exist;s<i>.</i>B:<br />
 * &rarr; [&exist;r<i>.</i>A &#8930; &exist;s<i>.</i>B]</li>
 * 
 * <li>3. For every pair &exist;r<i>.</i>A, &exist;r<i>.</i>B of atoms of
 * &Gamma;, we say that &exist;r<i>.</i>A can only be subsumed by
 * &exist;r<i>.</i>B if A is already subsumed by B:<br />
 * [A &#8930; B] &rarr; [&exist;r<i>.</i>A &#8930; &exist;r<i>.</i>B]</li>
 * 
 * <li>4. For every concept constant A and every atom &exist;r<i>.</i>B of
 * &Gamma;, we say that A and &exist;r<i>.</i>B are not in a subsumption
 * relationship<br />
 * &rarr; [A &#8930; &exist;r<i>.</i>B] and &rarr; [&exist;r<i>.</i>B &#8930; A]
 * </li>
 * 
 * <li>5. Transitivity of subsumption is expressed using the non-Horn clauses:<br />
 * [C<sub>1</sub> &#8930; C<sub>3</sub>] &rarr; [C<sub>1</sub> &#8930;
 * C<sub>2</sub>] &or; [C<sub>2</sub> &#8930; C<sub>3</sub>] where
 * C<sub>1</sub>, C<sub>2</sub>, C<sub>3</sub> are atoms of &Gamma;.<br />
 * </li>
 * </ul>
 * Note that there are further properties that hold for subsumption in <i>EL</i>
 * (e.g., the fact that A &#8849; B implies &exist;r<i>.</i>A &#8849;
 * &exist;r<i>.</i>B), but that are not needed to ensure soundness of our
 * translation.</li>
 * 
 * <li>(3) Translation of the relevant properties of &gt;.
 * 
 * <ul>
 * <li>1. Transitivity and irreexivity of &gt; can be expressed using the Horn
 * clauses:<br />
 * [X &gt; X] &rarr; and [X &gt; Y] &and; [Y &gt; Z] &rarr; [X &gt; Z],<br />
 * where X, Y, Z are concept variables occurring in &Gamma;.</li>
 * 
 * <li>2. The connection between this order and the order &gt;<sub>&sigma;</sub>
 * is expressed using the non-Horn clauses:<br />
 * &rarr; [X &gt; Y] &or; [X &#8930; &exist;r<i>.</i>Y],<br />
 * where X, Y are concept variables occurring in &Gamma; and &exist;r<i>.</i>Y
 * is an atom of &Gamma;.</li>
 * </ul>
 * </li>
 * </ul>
 * </div>
 * 
 * @author Barbara Morawska
 * @author Julian Mendez
 */
public class SatProcessor implements UelProcessor {

	private static final String keyConfiguration = "Configuration";
	private static final String keyName = "Name";
	private static final String keyNumberOfClauses = "Number of clauses";
	private static final String keyNumberOfPropositions = "Number of propositions";
	private static final String keyNumberOfVariables = "Number of variables";
	private static final Logger logger = Logger.getLogger(SatProcessor.class
			.getName());
	private static final String notUsingMinimalAssignments = "all local assignments";
	private static final String processorName = "SAT-based algorithm";
	private static final String usingMinimalAssignments = "only minimal assignments";

	private final ExtendedUelInput extUelInput;
	private boolean firstTime = true;
	private final boolean invertLiteral;
	private IndexedSet<Literal> literalManager = new IndexedSetImpl<Literal>();
	private long numberOfClauses = 0;
	private final boolean onlyMinimalAssignments;
	private UelOutput result;
	private Solver solver;
	private Map<Integer, Set<Integer>> subsumers = new HashMap<Integer, Set<Integer>>();
	private Set<Integer> trueLiterals = new HashSet<Integer>();
	private final UelInput uelInput;
	private Set<Integer> update = new HashSet<Integer>();
	private final boolean hasDisequations;

	/**
	 * Construct a new SAT processor to solve a unification problem.
	 * 
	 * @param input
	 *            the UEL input
	 * @param inv
	 *            a flag indicating whether inverted literals should be used
	 * @param useMinimalAssignments
	 */
	public SatProcessor(UelInput input, boolean inv,
			boolean useMinimalAssignments) {
		if (input == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		this.uelInput = input;
		this.extUelInput = new ExtendedUelInput(input);
		this.hasDisequations = (getDisequations() != null)
				&& !getDisequations().isEmpty();
		this.invertLiteral = inv;
		this.onlyMinimalAssignments = useMinimalAssignments;
		setLiterals();
	}

	private void addClausesForDissubsumptions(SatInput ret) {
		for (Integer x : getVariables()) {
			for (Integer d : getConstants()) {
				addClausesForDissubsumptions(ret, d, x);
			}
			for (Integer d : getEAtoms()) {
				addClausesForDissubsumptions(ret, d, x);
			}
		}
	}

	private void addClausesForDissubsumptions(SatInput ret, Integer d, Integer x) {
		Set<Integer> mainClause = new HashSet<Integer>();
		mainClause.add(getMinusSubOrDissubLiteral(d, x));
		for (Integer e : getConstants()) {
			addClausesForDissubsumptions(ret, d, x, e, mainClause);
		}
		for (Integer e : getEAtoms()) {
			addClausesForDissubsumptions(ret, d, x, e, mainClause);
		}
		ret.add(mainClause);
	}

	private void addClausesForDissubsumptions(SatInput ret, Integer d,
			Integer x, Integer e, Set<Integer> mainClause) {
		Integer p = getAuxiliaryLiteral(d, x, e);
		mainClause.add(p);

		Set<Integer> clause1 = new HashSet<Integer>();
		clause1.add((-1) * p);
		clause1.add(getMinusSubOrDissubLiteral(x, e));
		ret.add(clause1);

		Set<Integer> clause2 = new HashSet<Integer>();
		clause2.add((-1) * p);
		clause2.add(getSubOrDissubLiteral(d, e));
		ret.add(clause2);
	}

	private boolean addEntry(List<Map.Entry<String, String>> list, String key,
			String value) {
		return list
				.add(new AbstractMap.SimpleEntry<String, String>(key, value));
	}

	private void addSmallSubsumptions(SatInput input) {
		// TODO: remove?
		for (Equation e : getEquations()) {
			if (e.getRight().size() == 1) {
				Set<Integer> clause = new HashSet<Integer>();
				Integer subsumed = e.getRight().iterator().next();
				Integer subsuming = e.getLeft();
				clause.add(getMinusSubOrDissubLiteral(subsumed, subsuming));
				input.add(clause);
			}
		}
	}

	private boolean addToSetOfSubsumers(Integer atomId1, Integer atomId2) {
		Set<Integer> ret = this.subsumers.get(atomId1);
		if (ret == null) {
			ret = new HashSet<Integer>();
			this.subsumers.put(atomId1, ret);
		}
		return ret.add(atomId2);
	}

	private ConceptName asConceptName(Atom atom) {
		return (ConceptName) atom;
	}

	private ExistentialRestriction asExistentialRestriction(Atom atom) {
		return (ExistentialRestriction) atom;
	}

	@Override
	public boolean computeNextUnifier() {
		SatOutput satoutput = null;
		boolean unifiable = false;
		try {
			if (this.firstTime) {
				if (onlyMinimalAssignments) {
					solver = new Sat4jMaxSatSolver();
				} else {
					solver = new Sat4jSolver();
				}
				SatInput satInput = computeSatInput();
				numberOfClauses = satInput.getClauses().size();
				satoutput = solver.solve(satInput);
				unifiable = satoutput.isSatisfiable();
			} else {
				Set<Integer> update = getUpdate();
				if (update.isEmpty()) {
					unifiable = false;
				} else {
					numberOfClauses++;
					satoutput = solver.update(update);
					unifiable = satoutput.isSatisfiable();
				}
			}
		} catch (IOException e) {
			throw new RuntimeException(e);
		}

		reset();
		if (unifiable) {
			this.result = new UelOutputImpl(getAtomManager(),
					toTBox(satoutput.getOutput()));
		}

		this.firstTime = false;
		return unifiable;
	}

	/**
	 * This method encodes equations into propositional clauses in DIMACS CNF
	 * format, i.e. positive literal is represented by a positive number and a
	 * negative literal is represented by a corresponding negative number. Each
	 * clause is on one line. The end of a clause is marked by 0. Example of a
	 * clause in DIMACS format: 1 -3 0
	 * 
	 * @return an object representing the DIMACS CNF encoding of the input
	 *         subsumptions
	 */
	public SatInput computeSatInput() {
		SatInput ret = new SatInput();

		logger.finer("computing SAT input ...");

		logger.finer("running step 1 ...");
		runStep1(ret);

		logger.finer("running step 2.1 ...");
		runStep2_1(ret);

		logger.finer("running steps 2.2 and 2.3 ...");
		runSteps2_2_N_2_3(ret);

		logger.finer("running step 2.4 ...");
		runStep2_4(ret);

		logger.finer("running step 2.5 ...");
		runStep2_5(ret);

		logger.finer("running step 3.1 reflexivity ...");
		runStep3_1_r(ret);

		logger.finer("running step 3.1 transitivity ...");
		runStep3_1_t(ret);

		logger.finer("running step 3.2 ...");
		runStep3_2(ret);

		if (hasDisequations) {
			// add clauses with auxiliary variables needed for soundness of
			// disunification
			logger.finer("adding clauses for dissubsumptions ...");
			addClausesForDissubsumptions(ret);

			addSmallSubsumptions(ret);
		}

		if (onlyMinimalAssignments) {
			logger.finer("adding literals to be minimized ...");
			for (Integer var : getVariables()) {
				if (isUserVariable(var)) {
					for (Integer con : getConstants()) {
						Literal literal = invertLiteral ? new SubsumptionLiteral(
								var, con) : new DissubsumptionLiteral(var, con);
						Integer literalId = literalManager
								.addAndGetIndex(literal);
						ret.addMinimizeLiteral(literalId);
					}
					for (Integer eat : getEAtoms()) {
						Literal literal = invertLiteral ? new SubsumptionLiteral(
								var, eat) : new DissubsumptionLiteral(var, eat);
						Integer literalId = literalManager
								.addAndGetIndex(literal);
						ret.addMinimizeLiteral(literalId);
					}
				}
			}
		}

		logger.finer("SAT input computed.");

		return ret;
	}

	private Set<Integer> createUpdate() {
		Set<Integer> ret = new HashSet<Integer>();
		Set<Integer> set = new HashSet<Integer>();
		set.addAll(getConstants());
		set.addAll(getEAtoms());
		for (Integer firstAtomId : getVariables()) {
			Atom firstAtom = getAtomManager().get(firstAtomId);
			if (firstAtom.isConceptName() && isUserVariable(firstAtomId)) {
				for (Integer secondAtomId : set) {
					Literal literal = this.invertLiteral ? new SubsumptionLiteral(
							firstAtomId, secondAtomId)
							: new DissubsumptionLiteral(firstAtomId,
									secondAtomId);
					Integer literalId = literalManager.addAndGetIndex(literal);
					if (!onlyMinimalAssignments
							|| getLiteralValue(literalId) == this.invertLiteral) {
						ret.add(getLiteralValue(literalId) ? (-1) * literalId
								: literalId);
					}
				}
			}
		}
		return ret;
	}

	private IndexedSet<Atom> getAtomManager() {
		return this.extUelInput.getAtomManager();
	}

	private Integer getAuxiliaryLiteral(Integer d, Integer x, Integer e) {
		return literalManager.addAndGetIndex(new AuxiliaryLiteral(d, x, e));
	}

	private Set<Integer> getConstants() {
		return this.extUelInput.getConstants();
	}

	private Set<SmallEquation> getDisequations() {
		return this.extUelInput.getGoalDisequations();
	}

	private Set<Integer> getEAtoms() {
		return this.extUelInput.getEAtoms();
	}

	private Set<Equation> getEquations() {
		return this.extUelInput.getEquations();
	}

	public List<Map.Entry<String, String>> getInfo() {
		List<Map.Entry<String, String>> ret = new ArrayList<Map.Entry<String, String>>();
		addEntry(ret, keyName, processorName);

		if (onlyMinimalAssignments) {
			addEntry(ret, keyConfiguration, usingMinimalAssignments);
		} else {
			addEntry(ret, keyConfiguration, notUsingMinimalAssignments);
		}

		if (literalManager != null) {
			addEntry(ret, keyNumberOfPropositions, "" + literalManager.size());
		}
		addEntry(ret, keyNumberOfClauses, "" + numberOfClauses);
		addEntry(ret, keyNumberOfVariables, ""
				+ this.extUelInput.getVariables().size());
		return Collections.unmodifiableList(ret);
	}

	@Override
	public UelInput getInput() {
		return this.uelInput;
	}

	/**
	 * Returns the literals.
	 * 
	 * @return the literals
	 */
	public Set<Literal> getLiterals() {
		return Collections.unmodifiableSet(this.literalManager);
	}

	private boolean getLiteralValue(Integer literalId) {
		if (literalId == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		return this.trueLiterals.contains(literalId);
	}

	private Integer getMinusOrderLiteral(Integer atomId1, Integer atomId2) {
		return (-1) * getOrderLiteral(atomId1, atomId2);
	}

	private Integer getMinusSubOrDissubLiteral(Integer atomId1, Integer atomId2) {
		return (-1) * getSubOrDissubLiteral(atomId1, atomId2);
	}

	private Integer getOrderLiteral(Integer atomId1, Integer atomId2) {
		Literal literal = new OrderLiteral(atomId1, atomId2);
		return literalManager.addAndGetIndex(literal);
	}

	private Collection<Integer> getSetOfSubsumers(Integer atomId) {
		Set<Integer> list = this.subsumers.get(atomId);
		if (list == null) {
			list = new HashSet<Integer>();
			this.subsumers.put(atomId, list);
		}
		return Collections.unmodifiableCollection(list);
	}

	private Integer getSubOrDissubLiteral(Integer atomId1, Integer atomId2) {
		Literal literal = invertLiteral ? new SubsumptionLiteral(atomId1,
				atomId2) : new DissubsumptionLiteral(atomId1, atomId2);
		int val = literalManager.addAndGetIndex(literal);
		return invertLiteral ? (-1) * val : val;
	}

	@Override
	public UelOutput getUnifier() {
		return result;
	}

	private Set<Integer> getUpdate() {
		return Collections.unmodifiableSet(update);
	}

	private Set<Equation> getUpdatedUnifier() {
		Set<Equation> ret = new HashSet<Equation>();
		for (Integer leftPartId : getVariables()) {
			// Atom leftPart = getAtomManager().get(leftPartId);
			// if (leftPart.isConceptName()
			// && isUserVariable(leftPartId)) {
			ret.add(new EquationImpl(leftPartId, new HashSet<Integer>(
					getSetOfSubsumers(leftPartId)), false));
			// }
		}

		return ret;
	}

	private Set<Integer> getUsedAtomIds() {
		return this.extUelInput.getUsedAtomIds();
	}

	private Set<Integer> getVariables() {
		return this.extUelInput.getVariables();
	}

	private boolean isTop(Integer atomId) {
		Atom atom = getAtomManager().get(atomId);
		return (atom.isConceptName() && asConceptName(atom).isTop());
	}

	private boolean isUserVariable(Integer atomId) {
		return this.extUelInput.getUserVariables().contains(atomId);
	}

	/**
	 * Resets string update values for literals and S(X) for each X, before the
	 * next unifier is computed.
	 */
	public void reset() {

		update = new HashSet<Integer>();

		for (Integer key : literalManager.getIndices()) {
			setLiteralValue(key, false);
		}

		for (Integer atomId : getVariables()) {
			resetSetOfSubsumers(atomId);
		}
	}

	private void resetSetOfSubsumers(Integer atomId) {
		Set<Integer> list = this.subsumers.get(atomId);
		if (list == null) {
			list = new HashSet<Integer>();
			this.subsumers.put(atomId, list);
		}
		list.clear();
	}

	/**
	 * Clauses created in Step 1
	 */
	private void runStep1(SatInput input) {
		for (Equation e : getEquations()) {
			runStep1ForConstants(e, input);
			runStep1ForExistentialAtoms(e, input);
		}

		// goal disequations
		for (SmallEquation e : getDisequations()) {
			Set<Integer> clause = new HashSet<Integer>();
			clause.add(getSubOrDissubLiteral(e.getLeft(), e.getRight()));
			clause.add(getSubOrDissubLiteral(e.getRight(), e.getLeft()));
			input.add(clause);
		}
	}

	/**
	 * Step 1 for constants
	 * 
	 * @param e
	 *            equation
	 */
	private void runStep1ForConstants(Equation e, SatInput input) {
		for (Integer atomId1 : getConstants()) {

			if (!e.getLeft().equals(atomId1) && !e.getRight().contains(atomId1)) {

				Integer atomId2 = e.getLeft();

				/*
				 * constant not in the equation
				 * 
				 * one side of an equation
				 */

				for (Integer atomId3 : e.getRight()) {
					Set<Integer> clause = new HashSet<Integer>();
					clause.add(getMinusSubOrDissubLiteral(atomId2, atomId1));
					clause.add(getSubOrDissubLiteral(atomId3, atomId1));
					input.add(clause);
				}

				/*
				 * another side of an equation
				 */

				Set<Integer> clause = new HashSet<Integer>();
				for (Integer atomId3 : e.getRight()) {
					clause.add(getMinusSubOrDissubLiteral(atomId3, atomId1));
				}
				clause.add(getSubOrDissubLiteral(atomId2, atomId1));
				input.add(clause);

			} else if (!e.getLeft().equals(atomId1)
					&& e.getRight().contains(atomId1)) {

				/*
				 * constant of the right but not on the left
				 */

				Set<Integer> clause = new HashSet<Integer>();
				Integer atomId2 = e.getLeft();
				clause.add(getMinusSubOrDissubLiteral(atomId2, atomId1));
				input.add(clause);

			} else if (e.getLeft().equals(atomId1)
					&& !e.getRight().contains(atomId1)) {

				/*
				 * constant on the left but not on the right
				 */

				Set<Integer> clause = new HashSet<Integer>();
				for (Integer atomId3 : e.getRight()) {
					clause.add(getMinusSubOrDissubLiteral(atomId3, atomId1));
				}
				input.add(clause);
			}
		}
	}

	/**
	 * Step 1 for existential atoms
	 * 
	 * @param e
	 *            equation
	 */
	private void runStep1ForExistentialAtoms(Equation e, SatInput input) {
		for (Integer atomId1 : getEAtoms()) {

			if (!e.getLeft().equals(atomId1) && !e.getRight().contains(atomId1)) {

				/*
				 * atom not in the equation
				 * 
				 * one side of equation
				 */

				Integer atomId2 = e.getLeft();
				for (Integer atomId3 : e.getRight()) {
					Set<Integer> clause = new HashSet<Integer>();
					clause.add(getMinusSubOrDissubLiteral(atomId2, atomId1));
					clause.add(getSubOrDissubLiteral(atomId3, atomId1));
					input.add(clause);
				}

				/*
				 * another side of the equation
				 */

				Set<Integer> clause = new HashSet<Integer>();
				for (Integer atomId3 : e.getRight()) {
					clause.add(getMinusSubOrDissubLiteral(atomId3, atomId1));
				}
				clause.add(getSubOrDissubLiteral(atomId2, atomId1));
				input.add(clause);

			} else if (!e.getLeft().equals(atomId1)
					&& e.getRight().contains(atomId1)) {

				/*
				 * existential atom on the right but not on the left side of an
				 * equation
				 */

				Set<Integer> clause = new HashSet<Integer>();
				Integer atomId2 = e.getLeft();
				clause.add(getMinusSubOrDissubLiteral(atomId2, atomId1));
				input.add(clause);

				// end of outer if; key1 is not on the left, ask if it
				// is on the right
			} else if (e.getLeft().equals(atomId1)
					&& !e.getRight().contains(atomId1)) {

				/*
				 * existential atom on the left but not on the right side of
				 * equation
				 */

				Set<Integer> clause = new HashSet<Integer>();
				for (Integer atomId3 : e.getRight()) {
					clause.add(getMinusSubOrDissubLiteral(atomId3, atomId1));
				}
				input.add(clause);

			}
		}
	}

	/**
	 * Step 2.1
	 */
	private void runStep2_1(SatInput input) {
		for (Integer atomId1 : getConstants()) {

			for (Integer atomId2 : getConstants()) {
				if (!isTop(atomId2) && (!atomId1.equals(atomId2))) {
					Set<Integer> clause = new HashSet<Integer>();
					clause.add(getSubOrDissubLiteral(atomId1, atomId2));
					input.add(clause);
				}
			}

			if (hasDisequations) {
				// positive clause needed for soundness of disunification
				Set<Integer> clause = new HashSet<Integer>();
				clause.add(getMinusSubOrDissubLiteral(atomId1, atomId1));
				input.add(clause);
			}

		}
	}

	/**
	 * Step 2.4
	 */
	private void runStep2_4(SatInput input) {
		for (Integer atomId1 : getConstants()) {

			for (Integer atomId2 : getEAtoms()) {
				{
					Set<Integer> clause = new HashSet<Integer>();
					clause.add(getSubOrDissubLiteral(atomId1, atomId2));
					input.add(clause);
				}

				if (!isTop(atomId1)) {
					Set<Integer> clause = new HashSet<Integer>();
					clause.add(getSubOrDissubLiteral(atomId2, atomId1));
					input.add(clause);
				}

			}

		}
	}

	/**
	 * Step 2.5
	 * 
	 * Transitivity of dis-subsumption
	 */
	private void runStep2_5(SatInput input) {
		Collection<Integer> atomIds = getUsedAtomIds();

		for (Integer atomId1 : atomIds) {

			for (Integer atomId2 : atomIds) {

				if (!atomId1.equals(atomId2)) {
					for (Integer atomId3 : atomIds) {

						if (!atomId1.equals(atomId3)
								&& !atomId2.equals(atomId3)) {
							Set<Integer> clause = new HashSet<Integer>();
							clause.add(getSubOrDissubLiteral(atomId1, atomId2));
							clause.add(getSubOrDissubLiteral(atomId2, atomId3));
							clause.add(getMinusSubOrDissubLiteral(atomId1,
									atomId3));
							input.add(clause);
						}
					}
				}
			}
		}
	}

	/**
	 * Step 3.1
	 * 
	 * Reflexivity for order literals
	 */
	private void runStep3_1_r(SatInput input) {
		for (Integer atomId1 : getVariables()) {
			Set<Integer> clause = new HashSet<Integer>();
			clause.add(getMinusOrderLiteral(atomId1, atomId1));
			input.add(clause);
		}
	}

	/**
	 * Step 3.1
	 * 
	 * Transitivity for order literals
	 */
	private void runStep3_1_t(SatInput input) {
		for (Integer atomId1 : getVariables()) {

			for (Integer atomId2 : getVariables()) {

				for (Integer atomId3 : getVariables()) {

					if (!atomId1.equals(atomId2) && !atomId2.equals(atomId3)) {

						Set<Integer> clause = new HashSet<Integer>();
						clause.add(getMinusOrderLiteral(atomId1, atomId2));
						clause.add(getMinusOrderLiteral(atomId2, atomId3));
						clause.add(getOrderLiteral(atomId1, atomId3));
						input.add(clause);
					}

				}

			}

		}
	}

	/**
	 * Step 3.2 Disjunction between order literals and dis-subsumption
	 */
	private void runStep3_2(SatInput input) {
		for (Integer atomId1 : getEAtoms()) {

			Atom eatom = getAtomManager().get(atomId1);
			if (!eatom.isExistentialRestriction()) {
				throw new IllegalStateException();
			}
			Atom child = asExistentialRestriction(eatom).getChild();

			if (child.isConceptName() && asConceptName(child).isVariable()) {

				for (Integer atomId2 : getVariables()) {
					Set<Integer> clause = new HashSet<Integer>();
					Integer childId = getAtomManager().addAndGetIndex(child);
					clause.add(getOrderLiteral(atomId2, childId));
					clause.add(getSubOrDissubLiteral(atomId2, atomId1));
					input.add(clause);
				}
			}
		}
	}

	/**
	 * Step 2.2 and Step 2.3
	 */
	private void runSteps2_2_N_2_3(SatInput input) {
		for (Integer atomId1 : getEAtoms()) {

			for (Integer atomId2 : getEAtoms()) {

				if (!atomId1.equals(atomId2)) {

					ExistentialRestriction ex1 = asExistentialRestriction(getAtomManager()
							.get(atomId1));
					ExistentialRestriction ex2 = asExistentialRestriction(getAtomManager()
							.get(atomId2));
					Integer role1 = ex1.getRoleId();
					Integer role2 = ex2.getRoleId();

					/*
					 * if roles are not equal, then Step 2.2
					 */

					if (!role1.equals(role2)) {
						Set<Integer> clause = new HashSet<Integer>();
						clause.add(getSubOrDissubLiteral(atomId1, atomId2));
						input.add(clause);

						/*
						 * if the roles are equal, then clause in Step 2.3
						 */
					} else {

						Atom child1 = ex1.getChild();
						Integer child1Id = getAtomManager().addAndGetIndex(
								child1);

						Atom child2 = ex2.getChild();
						Integer child2Id = getAtomManager().addAndGetIndex(
								child2);

						if (!child1Id.equals(child2Id)) {
							Set<Integer> clause = new HashSet<Integer>();
							clause.add(getMinusSubOrDissubLiteral(child1Id,
									child2Id));
							clause.add(getSubOrDissubLiteral(atomId1, atomId2));
							input.add(clause);
						}

						if (hasDisequations) {
							// converse clause needed for soundness of
							// disunification
							Set<Integer> clause = new HashSet<Integer>();
							clause.add(getMinusSubOrDissubLiteral(atomId1,
									atomId2));
							clause.add(getSubOrDissubLiteral(child1Id, child2Id));
							input.add(clause);
						}

					}

				}

			}

		}
	}

	/**
	 * Creates dis-subsumptions and order literals from all pairs of atoms of
	 * the goal
	 */
	private void setLiterals() {

		/*
		 * Literals for dis-subsumptions
		 */

		for (Integer atomId1 : getUsedAtomIds()) {
			for (Integer atomId2 : getUsedAtomIds()) {
				Literal literal = invertLiteral ? new SubsumptionLiteral(
						atomId1, atomId2) : new DissubsumptionLiteral(atomId1,
						atomId2);

				literalManager.add(literal);
			}
		}

		/*
		 * 
		 * Literals for order on variables
		 */

		for (Integer atomId1 : getVariables()) {
			for (Integer atomId2 : getVariables()) {
				Literal literal = new OrderLiteral(atomId1, atomId2);
				literalManager.add(literal);
			}
		}
	}

	private void setLiteralValue(Integer literalId, boolean value) {
		if (literalId == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		if (value) {
			this.trueLiterals.add(literalId);
		} else {
			this.trueLiterals.remove(literalId);
		}
	}

	private void setValuesForLiterals(Set<Integer> val) {
		if (val == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		for (Integer currentLiteral : val) {
			if (currentLiteral < 0) {
				Integer i = (-1) * currentLiteral;
				Literal literal = literalManager.get(i);
				if (literal.isDissubsumption() || literal.isSubsumption()) {
					setLiteralValue(i, false);
				}
			} else if (currentLiteral > 0) {
				setLiteralValue(currentLiteral, true);
			}
		}
	}

	/**
	 * Updates the translator with the SAT solver output, returning a new
	 * unifier.
	 * 
	 * @param val
	 *            SAT solver output
	 * @return a new unifier.
	 */
	public Set<Equation> toTBox(Set<Integer> val) {
		setValuesForLiterals(val);
		updateTBox();
		update = createUpdate();
		Set<Equation> ret = getUpdatedUnifier();
		return Collections.unmodifiableSet(ret);
	}

	private void updateTBox() {
		/*
		 * Define S_X for each variable X
		 */

		for (Integer i : literalManager.getIndices()) {

			Integer atomId1 = literalManager.get(i).getFirst();
			Integer atomId2 = literalManager.get(i).getSecond();

			if (literalManager.get(i).isDissubsumption()) {

				if (!getLiteralValue(i)) {

					if (getVariables().contains(atomId1)) {
						if (getConstants().contains(atomId2)) {
							addToSetOfSubsumers(atomId1, atomId2);
						} else if (getEAtoms().contains(atomId2)) {
							addToSetOfSubsumers(atomId1, atomId2);
						}
					}
				}
			} else if (literalManager.get(i).isSubsumption()) {
				if (getLiteralValue(i)) {

					if (getVariables().contains(atomId1)) {
						if (getConstants().contains(atomId2)) {
							addToSetOfSubsumers(atomId1, atomId2);
						} else if (getEAtoms().contains(atomId2)) {
							addToSetOfSubsumers(atomId1, atomId2);
						}
					}

				}
			}
		}
	}

}
