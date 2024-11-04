package de.tudresden.inf.lat.uel.rule.rules;

import de.tudresden.inf.lat.uel.rule.Assignment;
import de.tudresden.inf.lat.uel.rule.FlatConstraint;
import de.tudresden.inf.lat.uel.rule.Result;
import de.tudresden.inf.lat.uel.type.api.Atom;

/**
 * This class implements the second part of the rule 'Eager Solving' of the
 * rule-based algorithm for unification in EL.
 * 
 * @author Stefan Borgwardt
 */
public final class EagerSolving2Rule extends EagerRule {

	@Override
	public Application getFirstApplication(FlatConstraint sub, Assignment assign) {
		if (!sub.isDissubsumption()) {
			Atom head = sub.getHead();
			for (Atom at : sub.getBody()) {
				if (at.isVariable()) {
					if (assign.getSubsumers(at).contains(head)) {
						return new Application();
					}
				}
			}
		}
		return null;
	}

	@Override
	public Result apply(FlatConstraint sub, Assignment assign, Application application) {
		System.out.println("ES2 has been applied" + sub);
		return new Result(sub, application);
	}

	@Override
	public String shortcut() {
		return "ES2";
	}

}
