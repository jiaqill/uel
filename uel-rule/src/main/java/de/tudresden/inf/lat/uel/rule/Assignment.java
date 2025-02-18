package de.tudresden.inf.lat.uel.rule;

import java.util.*;
import java.util.Map.Entry;
import java.util.concurrent.atomic.AtomicInteger;

import de.tudresden.inf.lat.uel.type.api.Atom;
import de.tudresden.inf.lat.uel.type.api.AtomManager;
import de.tudresden.inf.lat.uel.type.api.Goal;
import de.tudresden.inf.lat.uel.type.impl.ExistentialRestriction;

/**
 * An assignment of sets of non-variable atoms to variables. Such an assignment
 * should always be acyclic.
 *
 * @author Stefan Borgwardt
 */
public class Assignment {

	private final Map<Atom, Set<Atom>> subs = new HashMap<>();
	//private List<Atom> nonVariableAtoms;
	public Goal goal;
	public Map<Atom, List<Atom>> types = new HashMap<>();

	/**
	 * Create an empty assignment.
	 */
	Assignment() {}

	/**
	 * Create an assignment with a list of non-variable atoms.
	 *
	 //* @param nonVariableAtoms the list of non-variable atoms
	 */
	/*Assignment(List<Atom> nonVariableAtoms) {
		this.nonVariableAtoms = nonVariableAtoms;
	}*/

	public Assignment(Goal goal) {
		if (goal == null) {
			throw new IllegalArgumentException("Goal cannot be null!");
		}
		this.goal = goal;
		//this.nonVariableAtoms = nonVariableAtoms;
		this.types = new HashMap<>();
	}

	/**
	 * Create a copy of another assignment.
	 *
	 * @param other
	 *            the other assignment
	 */
	Assignment(Assignment other) {
		addAll(other);
		addAllTypes(other);
		//this.nonVariableAtoms = other.getNonVariableAtoms();
		this.goal = other.goal;
		/*this.types = new HashMap<>();
		for (Map.Entry<Atom, List<Atom>> entry : other.types.entrySet()) {
			this.types.put(entry.getKey(), new ArrayList<>(entry.getValue()));
		}*/
	}

	public List<Atom> getNonVariableAtoms() {
		//return Collections.unmodifiableList(nonVariableAtoms);
		//return this.nonVariableAtoms;
		return this.goal.getAtomManager().getNonvariableAtoms();
	}

	/**
	 * Add an atom to the assignment of a variable.
	 *
	 * @param var
	 *            the index of the variable
	 * @param at
	 *            the new atom
	 * @return true iff the assignment was changed as a result of this operation
	 */
	public boolean add(Atom var, Atom at) {
		if (at == null) {
			throw new IllegalArgumentException();
		}
		Set<Atom> flatAtoms = getOrInit(var);
		return flatAtoms.add(at);
	}

	/**
	 * Add a set of atoms to the assignment of a variable.
	 *
	 * @param var
	 *            the index of the variable
	 * @param at
	 *            the new atoms
	 * @return true iff the assignment was changed as a result of this operation
	 */
	public boolean addAll(Atom var, Set<Atom> at) {
		if (at == null)
			return false;
		Set<Atom> flatAtoms = getOrInit(var);
		return flatAtoms.addAll(at);
	}

	/**
	 * Add another variable assignment to this assignment.
	 *
	 * @param other
	 *            the assignment to be merged into this one
	 * @return true iff the assignment was changed as a result of this operation
	 */
	public boolean addAll(Assignment other) {
		if (other == null)
			return false;
		boolean ret = false;
		for (Entry<Atom, Set<Atom>> entry : other.subs.entrySet()) {
			if (addAll(entry.getKey(), entry.getValue()))
				ret = true;
		}
		return ret;
	}

	/**
	 * Remove a set of atoms from the assignment of a variable.
	 *
	 * @param var
	 *            the index of the variable
	 * @param at
	 *            the atoms to be removed
	 * @return true iff the assignment was changed as a result of this operation
	 */
	boolean removeAll(Atom var, Set<Atom> at) {
		if (at == null)
			return false;
		if (subs.get(var) == null)
			return false;
		return subs.get(var).removeAll(at);
	}

	/**
	 * Subtract another variable assignment from this assignment.
	 *
	 * @param other
	 *            the assignment to be removed from this one
	 * @return true iff the assignment was changed as a result of this operation
	 */
	boolean removeAll(Assignment other) {
		if (other == null)
			return false;
		boolean ret = false;
		for (Entry<Atom, Set<Atom>> entry : other.subs.entrySet()) {
			if (removeAll(entry.getKey(), entry.getValue()))
				ret = true;
		}
		return ret;
	}

	/**
	 * Retrieve the subsumers of a given variable according to this assignment.
	 *
	 * @param var
	 *            the variable
	 * @return the set of assigned subsumers
	 */
	public Set<Atom> getSubsumers(Atom var) {
		return getOrInit(var);
	}

	/**
	 * Retrieve the variable indices of the variables that are explicitly
	 * assigned some non-variable atoms by this assignment. This assignment
	 * might also be the empty set.
	 *
	 * @return a set containing the indices of all variables involved in this
	 *         assignment
	 */
	Set<Atom> getKeys() {
		return subs.keySet();
	}

	private Set<Atom> getOrInit(Atom var) {
		Set<Atom> flatAtoms = subs.get(var);
		if (flatAtoms == null) {
			flatAtoms = new HashSet<>();
			subs.put(var, flatAtoms);
		}
		return flatAtoms;
	}

	/**
	 * Check whether this assignment is empty.
	 *
	 * @return true iff no variable is assigned any subsumer
	 */
	boolean isEmpty() {
		for (Set<Atom> subsumers : subs.values()) {
			if (!subsumers.isEmpty())
				return false;
		}
		return true;
	}

	/**
	 * Add a set of atom types to the assignment of a variable.
	 *
	 * @param var the variable
	 * @param at the new types
	 * @return true iff the assignment was changed as a result of this operation
	 */
	public boolean addAllTypes(Atom var, Set<Atom> at) {
		if (at == null || at.isEmpty()) {
			return false;
		}
		List<Atom> typeList = getOrInitType(var);
		boolean changed = false;
		for (Atom atom : at) {
			if (!typeList.contains(atom)) {
				typeList.add(atom);
				changed = true;
			}
		}
		return changed;
	}

	/**
	 * Add another variable type assignment to this assignment.
	 *
	 * @param other the assignment to be merged into this one
	 * @return true iff the assignment was changed as a result of this operation
	 */
	public boolean addAllTypes(Assignment other) {
		if (other == null) {
			return false;
		}
		boolean changed = false;
		for (Entry<Atom, List<Atom>> entry : other.types.entrySet()) {
			if (addAllTypes(entry.getKey(), new HashSet<>(entry.getValue()))) {
				changed = true;
			}
		}
		return changed;
	}

	/**
	 * Get or initialize the type list for a variable.
	 *
	 * @param var the variable
	 * @return the initialized list of assigned types
	 */
	private List<Atom> getOrInitType(Atom var) {
		return types.computeIfAbsent(var, k -> new ArrayList<>());
	}


	/**
	 * Checks if there is a dependency of 'a' on 'b', i.e., whether 'b' is
	 * reachable from 'a' in the graph representation of the current assignment.
	 * It is important that the current assignment is acyclic; otherwise, this
	 * implementation might not terminate.
	 *
	 * @param a
	 *            the start variable
	 * @param b
	 *            the goal variable
	 * @return true iff 'a' depends on 'b'
	 */
	boolean dependsOn(Atom a, Atom b) {
		for (Atom at : getSubsumers(a)) {
			if (!at.isGround()) {
				Atom nextVar = at.getConceptName();
				if (nextVar.equals(b)) {
					return true;
				}
				if (dependsOn(nextVar, b)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Checks if a new assignment would make this assignment cyclic.
	 *
	 * @param var
	 *            the variable index
	 * @param at
	 *            the new atom
	 * @return true iff the resulting assignment would be cyclic
	 */
	public boolean makesCyclic(Atom var, Atom at) {
		if (at.isGround())
			return false;
		Atom conceptName = at.getConceptName();
		if (conceptName.equals(var))
			return true;
		return dependsOn(conceptName, var);
	}

	/**
	 * Checks if a new assignment would make this assignment cyclic.
	 *
	 * @param var
	 *            the variable index
	 * @param newAtoms
	 *            the new atoms
	 * @return true iff the resulting assignment would be cyclic
	 */
	public boolean makesCyclic(Atom var, Iterable<Atom> newAtoms) {
		for (Atom at : newAtoms) {
			if (makesCyclic(var, at)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public String toString() {
		StringBuffer buf = new StringBuffer();
		buf.append("[");
		for (Entry<Atom, Set<Atom>> e : subs.entrySet()) {
			buf.append(e.getKey());
			buf.append("=");
			buf.append(e.getValue());
			buf.append(";");
		}
		buf.append("]");
		return buf.toString();
	}

	// domain restrictions
	public boolean isCompatibleTypeAboutDomain(Atom var, Atom at) {
		if (goal == null) {
			throw new IllegalStateException("Goal has not been initialized!");
		}
		if (goal.getDomains() == null || goal.getDomains().isEmpty()) {
			System.out.println("goal.getDomains() == null!");
			return false; // Or return true, depending on your logic
		}

		Integer roleId = ((ExistentialRestriction)at).getRoleId();
		Set<Integer> domain = goal.getDomains().get(roleId);
		if (roleId.equals(goal.getAtomManager().getRoleId(goal.SNOMED_RoleGroup_URI()))) {
			domain = new HashSet<>(goal.getRoleGroupTypes().keySet()) ;
		}
		//Set<Integer> head = new HashSet<>();
		// If domain is null or empty, return false (or another logic)
		if (domain == null || domain.isEmpty()) {
			System.out.println("domain == null!");
			return false;
		}

		List<Atom> atomList = new ArrayList<>();
		for (Integer id : domain) {
			Atom atom = goal.getAtomManager().getAtom(id); // Translate integer to atom
			if (atom != null) {
				atomList.add(atom);
			}
		}
		List<Atom> originalTypes = types.get(var) != null ? new ArrayList<>(types.get(var)) : null;
		if (types.get(var) != null) {
			List<Atom> copy = new ArrayList<>(types.get(var));
			copy.retainAll(atomList); // keep only common elements
			if (!copy.isEmpty()) {
				types.put(var, copy);
				return true;
			} else {
				/*for (Atom type : originalTypes) {
					System.out.println("Types of "+ var + " "+ goal.getAtomManager().getIndex(type));
				}
				for (Integer d : domain) {
					System.out.println("Domain of "+ roleId + " "+ d);
				}
				System.out.println("");*/
				/*if (originalTypes != null) {
					types.put(var, originalTypes);
				} else {
					types.remove(var);
				}*/
				return false;
			}
		} else {
			types.put(var, atomList);
			return true;
		}
	}

	// range restrictions
	public boolean isCompatibleTypeAboutRange(Atom at) {
		Integer roleId = ((ExistentialRestriction)at).getRoleId();

		Atom child = at.getConceptName();
		if (!child.isVariable()) {
			return true;
		}
		Set<Integer> range = goal.getRanges().get(roleId);
		if (roleId.equals(goal.getAtomManager().getRoleId(goal.SNOMED_RoleGroup_URI()))) {
			range = new HashSet<>(goal.getRoleGroupTypes().values()) ;
		}
		List<Atom> atomList = new ArrayList<>();
		for (Integer id : range) {
			Atom atom = goal.getAtomManager().getAtom(id); // Translate integer to atom
			if (atom != null) {
				atomList.add(atom);
			}
		}
		if (types.get(child) != null) {
			List<Atom> copy = new ArrayList<>(types.get(child));
			copy.retainAll(atomList); // keep only common elements
			if (!copy.isEmpty()) {
				types.put(child, copy);
				return true;
			} else {
				return false;
			}
		} else {
			types.put(child, atomList);
			return true;
		}
	}

}
