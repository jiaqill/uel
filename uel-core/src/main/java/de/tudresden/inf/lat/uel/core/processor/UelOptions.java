/**
 * 
 */
package de.tudresden.inf.lat.uel.core.processor;

import org.semanticweb.owlapi.model.OWLClass;

/**
 * This class bundles all options to UEL.
 * 
 * @author Stefan Borgwardt
 */
public class UelOptions {

	/**
	 * Possible treatments for UNDEF names.
	 */
	public enum UndefBehavior {
		/**
		 * All UNDEF names are marked as user variables.
		 */
		USER_VARIABLES,
		/**
		 * All UNDEF names are marked as definition variables.
		 */
		INTERNAL_VARIABLES,
		/**
		 * All UNDEF names are marked as constants.
		 */
		CONSTANTS
	};

	/**
	 * Indicates whether 'SNOMED mode' is active. If yes, then certain
	 * syntactical restrictions are enabled, e.g., type compatibility and the
	 * number of occurrences of restrictions over the same role in one variable.
	 * 
	 * Default: false.
	 */
	public boolean snomedMode = false;

	/**
	 * Indicates how many RoleGroups to allow in the same substitution set
	 * (modulo subsumption). Only relevant for SNOMED.
	 * 
	 * Default: 0 (unlimited).
	 */
	public int numberOfRoleGroups = 0;

	/**
	 * Indicates whether UNDEF names are restricted to occur only in the context
	 * of their original definition.
	 * 
	 * Default: false.
	 */
	public boolean restrictUndefContext = false;

	/**
	 * Indicates whether to expand simple primitive definitions like A ⊑ B and
	 * introduce the auxiliary name A_UNDEF ('true'), or to simply make A a
	 * constant and not further expand the definition ('false').
	 * 
	 * Default: true.
	 */
	public boolean expandPrimitiveDefinitions = true;

	/**
	 * Indicates whether additional information about the unification process is
	 * printed.
	 * 
	 * Default: false.
	 */
	public boolean verbose = false;

	/**
	 * Designates an alias to be used to express 'owl:Thing', e.g., 'SNOMED CT
	 * Concept'.
	 * 
	 * Default: null (no alias).
	 */
	public OWLClass owlThingAlias = null;

	/**
	 * Indicates how the UNDEF names should be treated.
	 * 
	 * Default: USER_VARIABLES.
	 */
	public UndefBehavior undefBehavior = UndefBehavior.USER_VARIABLES;

	/**
	 * Indicates which algorithm should be used for unification.
	 * 
	 * Default: SAT_BASED_ALGORITHM.
	 */
	public String unificationAlgorithmName = UnificationAlgorithmFactory.SAT_BASED_ALGORITHM;

	
	public boolean minimize = false;
}
