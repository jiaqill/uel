package de.tudresden.inf.lat.uel.rule;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.tudresden.inf.lat.uel.rule.rules.*;
import de.tudresden.inf.lat.uel.rule.rules.Rule.Application;
import de.tudresden.inf.lat.uel.type.api.Atom;
import de.tudresden.inf.lat.uel.type.api.AtomManager;
import de.tudresden.inf.lat.uel.type.api.Definition;
import de.tudresden.inf.lat.uel.type.api.Goal;
import de.tudresden.inf.lat.uel.type.impl.AbstractUnificationAlgorithm;
import de.tudresden.inf.lat.uel.type.impl.DefinitionSet;
import de.tudresden.inf.lat.uel.type.impl.Unifier;

/**
 * This class is used to solve a disunification problem using a rule-based
 * unification algorithm for EL.
 *
 * This algorithm is described in: Franz Baader, Stefan Borgwardt, and Barbara
 * Morawska. 'Unification in the description logic EL w.r.t. cycle-restricted
 * TBoxes'. LTCS-Report 11-05, Chair for Automata Theory, Institute for
 * Theoretical Computer Science, Technische Universitaet Dresden, Dresden,
 * Germany, 2011. See https://lat.inf.tu-dresden.de/research/reports.html.
 *
 * Based on the algorithm in: Franz Baader and Barbara Morawska. 'Unification in
 * the description logic EL'. Logical Methods in Computer Science, 6(3), 2010.
 * Special Issue: 20th Int. Conf. on Rewriting Techniques and Applications
 * (RTA'09).
 *
 * @author Stefan Borgwardt
 */
public class RuleBasedUnificationAlgorithm extends AbstractUnificationAlgorithm {

	private static final String keyName = "Name";
	private static final String keyInitialCons = "Initial number of constraints";
	private static final String keyMaxCons = "Max. number of constraints (so far)";
	private static final String keyTreeSize = "Size of the search tree (so far)";
	private static final String keyDeadEnds = "Number of encountered dead ends (so far)";
	private static final String keyNumberOfVariables = "Number of variables";
	private static final String algorithmName = "Rule-based algorithm";

	private List<EagerRule> staticEagerRules;
	private List<EagerRule> dynamicEagerRules;
	private List<Rule> nondeterministicRules;

	private NormalizedGoal normalizedGoal;
	private Assignment assignment;
	private List<Atom> nonVariableAtoms;
	//private final int initialSize;
	private int treeSize = 1;
	private int deadEnds = 0;

	private Deque<Result> searchStack = null;

	/**
	 * Initialize a new disunification problem with goal subsumptions and dissubsumptions.
	 *
	 * @param goal
	 *            a UelInput object that will return the subsumptions and dissubsumptions to be
	 *            solved
	 */
	public RuleBasedUnificationAlgorithm(Goal goal) {
		super(goal);
		if (!goal.getTypes().isEmpty()) {
			throw new UnsupportedOperationException("The rule-based algorithm cannot deal with type information!");
		}
		this.normalizedGoal = null;
		this.nonVariableAtoms = goal.getAtomManager().getNonvariableAtoms();
		this.assignment = new Assignment(nonVariableAtoms);
		addInfo(keyName, algorithmName);
		addInfo(keyNumberOfVariables, goal.getAtomManager().getVariables().size());
		initRules();
	}

	@Override
	public void cleanup() {
		// reset computation of results
		searchStack = null;
	}

	@Override
	protected void updateInfo() {
		addInfo(keyMaxCons, normalizedGoal.getMaxSize());
		addInfo(keyTreeSize, treeSize);
		addInfo(keyDeadEnds, deadEnds);
	}

	/**
	 * Initialize the rule lists according to the rule-based algorithm for
	 * unification in EL w.r.t. the empty TBox.
	 */
	private void initRules() {
		staticEagerRules = new ArrayList<>();
		staticEagerRules.add(new EagerGroundSolvingRule());
		staticEagerRules.add(new EagerSolving1Rule());
		staticEagerRules.add(new EagerConflictRule());
		staticEagerRules.add(new EagerTopSolvingRule());
		staticEagerRules.add(new EagerAtomicDecomposition0());
		staticEagerRules.add(new EagerAtomicDecomposition1());

		dynamicEagerRules = new ArrayList<>();
		dynamicEagerRules.add(new EagerSolving2Rule());
		dynamicEagerRules.add(new EagerExtensionRule());
		dynamicEagerRules.add(new EagerLeftDecomposition());
		dynamicEagerRules.add(new EagerAtomicDecomposition2());

		nondeterministicRules = new ArrayList<>();
		nondeterministicRules.add(new DecompositionRule());
		nondeterministicRules.add(new ExtensionRule());
		nondeterministicRules.add(new RightDecomposition());
		nondeterministicRules.add(new LocalExtension());
	}

	/**
	 * If at least one unifier has already been computed, this method tries to
	 * compute the next unifier. If there are no more unifiers, 'false' is
	 * returned.
	 *
	 * @return true iff the current assignment represents a unifier of the goal
	 *         subsumptions and dissubsumptions
	 */
	public boolean computeNextUnifier() throws InterruptedException {
		if (normalizedGoal == null) {
			normalizedGoal = new NormalizedGoal(goal);
			addInfo(keyInitialCons, normalizedGoal.size());
			for (FlatConstraint con : normalizedGoal) {
				if (!con.isDissubsumption()) {
					if (con.getHead().isVariable()) {
						// subsumptions with a variable on the right-hand side are
						// always solved
						con.setSolved(true);
					}
				}
				else {
					if (con.getBody().size() == 1 && con.getDissubsumptionHead().size() == 1) {
						if (con.getBody().get(0).isVariable() && !con.getDissubsumptionHead().get(0).isVariable()) {
							// dissubsumptions with a variable on the left-hand side and a non-variable atom
							// on the right-hand aide are always solved
							con.setSolved(true);
						}
					}
				}
			}
			callbackPreprocessing();
		}

		if (searchStack == null) {
			searchStack = new ArrayDeque<>();

			// apply eager rules to each unsolved subsumption
			Result res = applyEagerRules(normalizedGoal, staticEagerRules, null);
			if (!res.wasSuccessful())
				return false;
			for (FlatConstraint con : res.getSolvedConstraints()) {
				con.setSolved(true);
			}
			Assignment tmp = new Assignment(nonVariableAtoms);
			res = applyEagerRules(normalizedGoal, dynamicEagerRules, tmp);
			if (!res.wasSuccessful())
				return false;
			if (!commitResult(res, tmp)) {
				return false;
			}

			// exhaustively apply eager rules to the result of this initial
			// iteration
			if (!applyEagerRules(res)) {
				return false;
			}
		} else {
			// we already have a search stack --> try to backtrack from last
			// solution
			if (!backtrack()) {
				return false;
			}
		}
		return solve();

	}

	@Override
	public Unifier getUnifier() {
		// convert current assignment to a set of definitions
		AtomManager atomManager = goal.getAtomManager();
		DefinitionSet definitions = new DefinitionSet(atomManager.getVariables().size());
		for (Integer varId : atomManager.getVariables()) {
			Set<Integer> body = new HashSet<>();
			for (Atom subsumer : assignment.getSubsumers(atomManager.getAtom(varId))) {
				body.add(atomManager.getIndex(subsumer));
			}
			definitions.add(new Definition(varId, Collections.unmodifiableSet(body), false));
		}
		return new Unifier(definitions);
	}

	private boolean solve() throws InterruptedException {
		while (true) {

			if (Thread.interrupted()) {
				throw new InterruptedException();
			}

			FlatConstraint con = chooseUnsolvedConstraint();
			if (con == null)
				return true;
			if (applyNextNondeterministicRule(con, null))
				continue;
			deadEnds++;
			if (!backtrack())
				return false;
		}
	}

	private boolean backtrack() {
		while (!searchStack.isEmpty()) {
			Result res = searchStack.pop();
			rollBackResult(res);
			if (applyNextNondeterministicRule(res.getConstraint(), res.getApplication())) {
				return true;
			}
		}
		return false;
	}

	private FlatConstraint chooseUnsolvedConstraint() {
		for (FlatConstraint con : normalizedGoal) {
			if (!con.isSolved())
				return con;
		}
		return null;
	}

	private Result applyEagerRules(Collection<FlatConstraint> cons, List<EagerRule> rules,
								   Assignment currentAssignment) {
		Result res = new Result(null, null);
		for (FlatConstraint con : cons) {
			if (!con.isSolved()) {
				for (Rule rule : rules) {
					Result r = tryApplyRule(con, rule, null, currentAssignment);
					if (r == null) {
						//res.getNewUnsolvedConstraints().add(con);
						continue;
					}
					if (!r.wasSuccessful())
						return r;
					res.getSolvedConstraints().add(con);
					res.getNewSubsumers().addAll(r.getNewSubsumers());
					res.getNewUnsolvedConstraints().addAll(r.getNewUnsolvedConstraints());
					if (currentAssignment != null) {
						currentAssignment.addAll(r.getNewSubsumers());
					}
					break;
				}
			}
		}
		return res;
	}

	private boolean applyNextNondeterministicRule(FlatConstraint con, Rule.Application previous) {
		Iterator<Rule> iter = nondeterministicRules
				.listIterator((previous == null) ? 0 : nondeterministicRules.indexOf(previous.rule()));

		while (iter.hasNext()) {
			Rule rule = iter.next();
			while (true) {
				Result res = tryApplyRule(con, rule, previous, assignment);
				if (res == null) {
					break;
				}
				previous = res.getApplication();
				if (!res.wasSuccessful()) {
					continue;
				}

				// now 'res' is the result of a successful nondeterministic rule
				// application ->
				// apply eager rules, put result on the stack
				if (!commitResult(res, null)) {
					// application of static eager rules failed -> roll back
					// changes and continue search
					deadEnds++;
					rollBackResult(res);
					continue;
				}

				if (!applyEagerRules(res)) {
					// exhaustive application of eager rules failed
					deadEnds++;
					rollBackResult(res);
					continue;
				}

				searchStack.push(res);
				treeSize++;
				return true;
			}
			previous = null;
		}
		return false;
	}

	/**
	 * Exhaustively apply all applicable eager rules to the goal subsumptions and dissubsumptions.
	 *
	 * @param parent
	 *            the previous result of a nondeterministic rule application to
	 *            which the results of the eager rule applications should be
	 *            added; if it is 'null', then no results are stored
	 * @return true iff all rule applications were successful
	 */
	private boolean applyEagerRules(Result parent) {
		Result currentResult = parent;
		Result nextResult = new Result(null, null);
		Assignment tmp = new Assignment(assignment);
		//currentResult = applyEagerRules(currentResult.getNewUnsolvedConstraints(), staticEagerRules, tmp);

		//System.out.println(tmp);

		do {

			// apply dynamic eager rules to each new unsolved subsumption and dissubsumption
			{
				Result res2 = applyEagerRules(currentResult.getNewUnsolvedConstraints(), dynamicEagerRules, tmp);
				//System.out.println("2unsolved constraints: " + res2.getNewUnsolvedConstraints());
				if (!res2.wasSuccessful())
					return false;
				nextResult.getSolvedConstraints().addAll(res2.getSolvedConstraints());
				nextResult.getNewUnsolvedConstraints().addAll(res2.getNewUnsolvedConstraints());
				nextResult.getNewSubsumers().addAll(res2.getNewSubsumers());
			}

			// apply dynamic eager rules for each new assignment
			Assignment newSubsumers = currentResult.getNewSubsumers();
			//Assignment newSubsumers = nextResult.getNewSubsumers();
			for (Atom var : newSubsumers.getKeys()) {
				if (!newSubsumers.getSubsumers(var).isEmpty()) {
					Result res = applyEagerRules(normalizedGoal.getConstraintsByBodyVariable(var), dynamicEagerRules, tmp);
					if (!res.wasSuccessful())
						return false;
					nextResult.getSolvedConstraints().addAll(res.getSolvedConstraints());
					nextResult.getNewUnsolvedConstraints().addAll(res.getNewUnsolvedConstraints());
					nextResult.getNewSubsumers().addAll(res.getNewSubsumers());
				}
			}

			boolean commitSuccessful = commitResult(nextResult, tmp);
			parent.amend(nextResult);
			if (!commitSuccessful)
				return false;

			currentResult = nextResult;
			nextResult = new Result(null, null);
			tmp = new Assignment(assignment);
		} while (!currentResult.getNewSubsumers().isEmpty() || !currentResult.getNewUnsolvedConstraints().isEmpty());

		return true;
	}

	/**
	 * Try to apply a rule to a given subsumption.
	 *
	 * @param rule
	 *            the rule to be applied
	 * @param con
	 *            the considered subsumption or dissubsumption
	 * @param previous
	 *            the previous result or 'null' if this is the first try
	 * @param currentAssignment
	 *            current assignment
	 * @return the result of the rule application or 'null' if no more rule
	 *         applications are possible
	 */
	private Result tryApplyRule(FlatConstraint con, Rule rule, Application previous, Assignment currentAssignment) {
		Rule.Application next;
		if (previous == null) {
			next = rule.getFirstApplication(con, currentAssignment);
		} else {
			next = rule.getNextApplication(con, currentAssignment, previous);
		}
		if (next == null) {
			return null;
		}

		Result res = rule.apply(con, currentAssignment, next);
		return res;
	}

	/**
	 * Adds the new unsolved subsumptions and dissubsumptions resulting from a rule application to
	 * the current goal and also applies the changes to the current assignment.
	 * In the process, the result is changed to reflect the exact changes that
	 * are made. For example, a created subsumption that is already in the goal
	 * is removed from the result. Additionally, the result of goal expansion is
	 * added to the result.
	 *
	 * @param res
	 *            the result to be considered; will be changed in-place
	 * @param newAssignment
	 *            the new assignment that will replace the current assignment;
	 *            if this is 'null', then the change will be computed from
	 *            'res.getNewSubsumers()'
	 * @return <code>true</code> if and only if the execution was successful
	 */
	private boolean commitResult(Result res, Assignment newAssignment) {
		// solve subsumption that triggered the rule
		if (res.getConstraint() != null) {
			res.getConstraint().setSolved(true);
		}

		// add new unsolved constraints to the goal
		res.getNewUnsolvedConstraints().removeAll(normalizedGoal);
		normalizedGoal.addAll(res.getNewUnsolvedConstraints());
		for (FlatConstraint con : res.getNewUnsolvedConstraints()) {
			if (!con.isDissubsumption()) {
				if (con.getHead().isVariable()) {
					// subsumptions with a variable on the right-hand side are
					// always solved
					con.setSolved(true);
					res.getNewSolvedConstraints().add(con);
				}
			}
			else {
				if (con.getBody().size() == 1 && con.getDissubsumptionHead().size() == 1) {
					if (con.getBody().get(0).isVariable() && !con.getDissubsumptionHead().get(0).isVariable()) {
						con.setSolved(true);
						res.getNewSolvedConstraints().add(con);
					}
				}
			}
		}
		res.getNewUnsolvedConstraints().removeAll(res.getNewSolvedConstraints());

		// goal expansion (I)
		for (FlatConstraint con : res.getNewSolvedConstraints()) {
			if (!con.isDissubsumption()) {
				/*
				 * we can assume that all new solved subsumptions have a variable in
				 * the head
				 */
				Set<FlatConstraint> newSubs = normalizedGoal.expand(con, assignment.getSubsumers(con.getHead()));
				res.getNewUnsolvedConstraints().addAll(newSubs);
			}
			else {
				Set<FlatConstraint> newSubs = normalizedGoal.expand(con, assignment.getSubsumers(con.getBody().get(0)));
				res.getNewUnsolvedConstraints().addAll(newSubs);
			}
		}

		// solve subsumptions and dissubsumptions in 'res.solvedConstraints'
		for (FlatConstraint con : res.getSolvedConstraints()) {
			con.setSolved(true);
		}

		// update current assignment
		res.getNewSubsumers().removeAll(assignment);
		if (newAssignment == null) {
			assignment.addAll(res.getNewSubsumers());
		} else {
			assignment = newAssignment;
		}

		// goal expansion (II)
		Set<FlatConstraint> newCons = normalizedGoal.expand(res.getNewSubsumers());
		res.getNewUnsolvedConstraints().addAll(newCons);

		// try to solve new unsolved subsumptions and dissubsumptions by static eager rules
		Result eagerRes = applyEagerRules(res.getNewUnsolvedConstraints(), staticEagerRules, null);
		if (!eagerRes.wasSuccessful())
			return false;

		for (FlatConstraint con : eagerRes.getSolvedConstraints()) {
			con.setSolved(true);
		}

		res.amend(eagerRes);
		return true;
	}

	/**
	 * Undo the changes made to the goal by a result.
	 *
	 * @param res
	 *            the result to undo
	 */
	private void rollBackResult(Result res) {

		assignment.removeAll(res.getNewSubsumers());
		normalizedGoal.removeAll(res.getNewSolvedConstraints());
		normalizedGoal.removeAll(res.getNewUnsolvedConstraints());

		for (FlatConstraint con : res.getSolvedConstraints()) {
			con.setSolved(false);
		}

		res.getConstraint().setSolved(false);
	}

}
