package de.tudresden.inf.lat.uel.rule.rules;

import de.tudresden.inf.lat.uel.rule.Assignment;
import de.tudresden.inf.lat.uel.rule.FlatConstraint;
import de.tudresden.inf.lat.uel.rule.Result;
import de.tudresden.inf.lat.uel.type.api.Atom;
import de.tudresden.inf.lat.uel.type.api.Goal;
import de.tudresden.inf.lat.uel.type.impl.ConceptName;
import de.tudresden.inf.lat.uel.type.impl.ExistentialRestriction;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * This class implements the rule 'Eager Extension' of the rule-based algorithm
 * for unification in EL.
 * 
 * @author Stefan Borgwardt
 */
public final class EagerExtensionRule extends EagerRule {

	@Override
	public Application getFirstApplication(FlatConstraint sub, Assignment assign) {
		if (!sub.isDissubsumption()) {
			// extract a variable from the body of sub
			// if there is more than one such variable, this rule does not apply
			Atom var = null;
			for (Atom at : sub.getBody()) {
				if (at.isVariable()) {
					if ((var != null) && (!var.equals(at))) {
						// two different variables have beend found
						return null;
					}
					var = at;
				}
			}
			if (var == null) {
				// no variable has been found
				return null;
			}
			// check whether the rest of the body is contained in the assignment of
			// the variable
			for (Atom at : sub.getBody()) {
				if (!at.isVariable() && !assign.getSubsumers(var).contains(at)) {
					return null;
				}
			}
			return new Application(var);
		}
		return null;
	}

	@Override
	public Result apply(FlatConstraint sub, Assignment assign, Rule.Application application) {
		if (!(application instanceof Application)) {
			throw new IllegalArgumentException("Expected rule application of type EagerExtensionRule.Application.");
		}
		Application appl = (Application) application;
		if (assign.makesCyclic(appl.var, sub.getHead())) {
			//System.out.println("DEBUG: Make cyclic!");
			return new Result(sub, application, false);
		}
		if (sub.getHead().isExistentialRestriction()){
			// domain and range restrictions
			boolean cDomain = assign.isCompatibleTypeAboutDomain(appl.var, sub.getHead());
			boolean cRange = assign.isCompatibleTypeAboutRange(sub.getHead());
			if (!cDomain || !cRange) {
				System.out.println("DEBUG: Domain or range not compatible! " + cDomain + cRange);
				return new Result(sub, application, false);
				//return null;
			}
		}

		Result res = new Result(sub, application);
		res.getNewSubsumers().add(appl.var, sub.getHead());
		//System.out.println("EEx has been applied" + sub);
		return res;
	}

	@Override
	String shortcut() {
		return "EEx";
	}

	private final class Application extends Rule.Application {

		protected Atom var;

		protected Application(Atom var) {
			this.var = var;
		}

		@Override
		public String toString() {
			return "EEx/" + var;
		}

	}

}
