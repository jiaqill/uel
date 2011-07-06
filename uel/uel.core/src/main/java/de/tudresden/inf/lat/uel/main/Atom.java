package de.tudresden.inf.lat.uel.main;

import java.io.PrintWriter;
import java.util.HashMap;

/**
 * This class implement an object atom. Atom is a concept term, which is not a
 * conjunction. Hence atom can be a concept name or an existential restriction.
 * 
 * 
 * 
 * @author morawska
 * 
 */

public class Atom {

	/*
	 * Atom has a name. If it is a concept name, this concept name is the
	 * <code>name</code>. If it is an existential restriction, then its role name is the
	 * <code>name</code>. In the case of existential restriction, the variable <code>root</code> is
	 * true and the hash map children implements conjunction of atoms that is an
	 * argument for the role name.
	 */

	final private String name;

	final private boolean root;

	private HashMap<String, Atom> children;

	/**
	 * Constructor used by the constructor of FAtom. n is a name of an atom and
	 * r is true if the atom is an existential restriction.
	 * 
	 * @param n
	 * @param r
	 */
	public Atom(String n, boolean r) {
		name = n;
		root = r;
	}

	/**
	 * Constructor used by ReaderAndParser and Ontology to construct a non-flat
	 * atom. n is the name of the atom r is true if the atom is an existential
	 * restriction argchild is the conjunction of atoms, which is an argument
	 * for the role name when r is true
	 * 
	 * @param n
	 * @param r
	 * @param argchild
	 */
	public Atom(String n, boolean r, HashMap<String, Atom> argchild) {

		name = n;
		children = argchild;
		root = r;

	}

	/**
	 * Returns name of the atom.
	 * 
	 * @return name of the atom
	 */
	public String getName() {

		return name;
	}

	/**
	 * Is true if the atom is an existential restriction.
	 * 
	 * @return <code>true</code> if and only if the atom is an existential restriction
	 */
	public boolean isRoot() {

		return root;
	}

	/**
	 * Checks if the atom is flat. Used by the constructor FAtom(Atom).
	 * 
	 * @return <code>true</code> if and only if the atom is flat
	 */
	public boolean isFlat() {

		boolean test = true;

		if (isRoot()) {

			if (children.size() == 1) {

				for (String key : children.keySet()) {

					if (children.get(key).isRoot()) {
						test = false;
					}

				}

			} else {
				test = false;
			}

		}
		return test;

	}

	/**
	 * Returns the hash map representing a conjunction of atoms, which is an
	 * argument for a role name in an existential atom.
	 * 
	 * @return the hash map representing a conjunction of atoms
	 */
	public HashMap<String, Atom> getChildren() {

		if (root) {
			return children;
		} else {

			System.out
					.println("WARNING: Cannot return children of a variable or constant");

			return null;
		}

	}

	@Override
	public String toString() {

		StringBuilder str = new StringBuilder(name);

		if (children != null) {
			str.append("[");
			for (String atom : children.keySet()) {

				str.append(children.get(atom).toString());

				str.append("  ");
			}
			str.append("]");
		}

		return str.toString();

	}

	/**
	 * 
	 * This method is not used by UEL. It is here for testing purposes.
	 * Prints atom to a Print Writer out.
	 * 
	 * 
	 * @param out
	 */
	public void print(PrintWriter out) {

		out.print(this.toString());

	}

}