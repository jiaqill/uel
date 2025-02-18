package de.tudresden.inf.lat.uel.rule;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.tudresden.inf.lat.uel.rule.rules.Rule.Application;

/**
 * Instances of this class describe the result of applying a rule of the
 * rule-based unification algorithm for EL to a constraint. In particular, they
 * specify newly created constraints and new assignments.
 * 
 * @author Stefan Borgwardt
 */
public final class Result<T> {

	private final T trigger;
	private final Application application;
	/*private final Set<FlatConstraint> newUnsolvedConstraints = new HashSet<>();
	private final Set<FlatConstraint> newSolvedConstraints = new HashSet<>();
	private final Set<FlatConstraint> solvedConstraints = new HashSet<>();*/
	private final Set<FlatConstraint> newUnsolvedConstraints = new HashSet<>();
	private final Set<FlatConstraint> newSolvedConstraints = new HashSet<>();
	private final Set<FlatConstraint> solvedConstraints = new HashSet<>();
	private final Assignment newSubsumers = new Assignment();
	private boolean successful;

	/**
	 * Construct a new rule application result.
	 * 
	 * @param trigger
	 *            the constraint that triggered the rule application
	 * @param application
	 *            the rule application
	 * @param successful
	 *            a flag indicating whether the rule application was successful
	 */
	public Result(T trigger, Application application, boolean successful) {
		this.trigger = trigger;
		this.application = application;
		this.successful = successful;
	}

	/**
	 * Construct a new rule application result, assuming that the application
	 * was successful.
	 * 
	 * @param trigger
	 *            the constraint that triggered the rule application
	 * @param application
	 *            the rule application
	 */
	public Result(T trigger, Application application) {
		this(trigger, application, true);
	}

	/**
	 * Adds the given result to this instance by appropriately merging the sets
	 * of new constraints and the new assignments.
	 * 
	 * @param res
	 *            the result that is to be added to the current result
	 */
	void amend(Result<T> res) {
		if (res.trigger instanceof FlatConstraint) {
			solveConstraint((FlatConstraint) res.trigger);
		}

		newUnsolvedConstraints.addAll(res.newUnsolvedConstraints);
		newSolvedConstraints.addAll(res.newSolvedConstraints);

		// Iterate through solved constraints and cast explicitly
		for (FlatConstraint sub : res.solvedConstraints) {
			solveConstraint(sub);
		}

		newSubsumers.addAll(res.newSubsumers);
	}

	private void solveConstraint(FlatConstraint sub) {
		if (newUnsolvedConstraints.remove(sub)) {
			newSolvedConstraints.add(sub);
		} else {
			solvedConstraints.add(sub);
		}

	}

	/**
	 * Return the constraint that triggered the rule application.
	 * 
	 * @return the triggering constraint
	 */
	T getConstraint() {
		return trigger;
	}

	/*Atom getAtom() {
		if (trigger instanceof Atom) {
			return (Atom) trigger;
		}
		return null;
	}*/

	/**
	 * Return the rule application that led to this result.
	 * 
	 * @return the rule application
	 */
	Application getApplication() {
		return application;
	}

	/**
	 * Return a flag indicating whether the rule application was successful.
	 * 
	 * @return 'false' iff the rule application failed
	 */
	boolean wasSuccessful() {
		return successful;
	}

	/**
	 * Set the success status of this rule application result.
	 * 
	 * @param value
	 *            a flag indicating whether the rule application was successful
	 */
	void setSuccessful(boolean value) {
		successful = value;
	}

	/**
	 * Retrieve the new assignments that resulted from the rule application or
	 * subsequent applications of eager rules.
	 * 
	 * @return an object specifying new non-variable atoms that were assigned to
	 *         variables
	 */
	public Assignment getNewSubsumers() {
		return newSubsumers;
	}

	/**
	 * Retrieve the new unsolved constraints that resulted from the rule
	 * application or subsequent applications of eager rules.
	 * 
	 * @return a set of new unsolved constraints
	 */
	public Set<FlatConstraint> getNewUnsolvedConstraints() {
		return newUnsolvedConstraints;
	}

	/**
	 * Retrieve the new unsolved constraints that resulted from the rule
	 * application or subsequent applications of eager rules.
	 * 
	 * @return a set of new unsolved constraints
	 */
	public Set<FlatConstraint> getNewSolvedConstraints() {
		return newSolvedConstraints;
	}

	/**
	 * Retrieve the solved constraints that resulted from the rule application
	 * or subsequent applications of eager rules.
	 *
	 * @return a set of solved constraints
	 */
	Set<FlatConstraint> getSolvedConstraints() {
		return solvedConstraints;
	}

	@Override
	public String toString() {
		StringBuffer buf = new StringBuffer();
		buf.append("{");
		buf.append(trigger);
		buf.append(",");
		buf.append(application);
		buf.append(",");
		buf.append(successful);
		buf.append(",");
		buf.append(newUnsolvedConstraints);
		buf.append(",");
		buf.append(newSolvedConstraints);
		buf.append(",");
		buf.append(solvedConstraints);
		buf.append(",");
		buf.append(newSubsumers);
		buf.append("}");
		return buf.toString();
	}

}
