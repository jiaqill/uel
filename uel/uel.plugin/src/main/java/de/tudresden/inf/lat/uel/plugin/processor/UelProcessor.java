package de.tudresden.inf.lat.uel.plugin.processor;

import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLOntology;

import de.tudresden.inf.lat.uel.core.sat.Sat4jSolver;
import de.tudresden.inf.lat.uel.core.sat.SatInput;
import de.tudresden.inf.lat.uel.core.sat.Solver;
import de.tudresden.inf.lat.uel.core.sat.Translator;
import de.tudresden.inf.lat.uel.core.type.Atom;
import de.tudresden.inf.lat.uel.core.type.Equation;
import de.tudresden.inf.lat.uel.core.type.Goal;
import de.tudresden.inf.lat.uel.core.type.Ontology;

/**
 * This class connects with UEL.
 * 
 * @author Julian Mendez
 */
public class UelProcessor {

	private Set<String> candidates = new HashSet<String>();
	private Ontology ontology = new Ontology();
	private SatInput satinput = null;
	private Translator translator = null;
	private List<String> unifierList = new ArrayList<String>();
	private Set<String> unifierSet = new HashSet<String>();

	public UelProcessor() {
	}

	public void addAll(Set<String> set) {
		if (set == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		this.candidates.addAll(set);
	}

	public void clearCandidates() {
		this.candidates.clear();
	}

	public void clearOntology() {
		this.ontology.clear();
		this.candidates.clear();
		this.unifierList.clear();
		this.unifierSet.clear();
	}

	public boolean computeNextUnifier() {
		boolean unifiable = false;
		Solver solver = new Sat4jSolver();
		StringWriter result = new StringWriter();
		String satoutputStr = null;
		try {
			if (getUnifierList().isEmpty()) {
				this.satinput = this.translator.getSatInput();
			} else {
				this.satinput.add(this.translator.getUpdate().toString());
			}
			satoutputStr = solver.solve(this.satinput.toString());
			this.translator.reset();
			unifiable = this.translator.toTBox(new StringReader(satoutputStr),
					result);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		result.flush();
		String res = result.toString();
		if (this.unifierSet.contains(res)) {
			unifiable = false;
		}
		if (unifiable) {
			this.unifierList.add(res);
			this.unifierSet.add(res);
		}
		return unifiable;
	}

	public Goal configure(Set<String> input) {
		if (input == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		Goal ret = createGoal(this.ontology, input, this.candidates);
		this.translator = new Translator(ret);
		return ret;
	}

	private Goal createGoal(Ontology ont, Set<String> input, Set<String> vars) {
		List<Equation> equationList = new ArrayList<Equation>();
		for (String cls : input) {
			Equation equation = ont.getDefinition(cls);
			if (equation == null) {
				equation = ont.getPrimitiveDefinition(cls);
			}
			if (equation != null) {
				equationList.add(equation);
			}
		}

		Goal ret = new Goal(ont);
		try {
			ret.initialize(equationList, createMainEquation(input), vars);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}

		return ret;
	}

	private Equation createMainEquation(Set<String> input) {
		Iterator<String> inputIt = input.iterator();
		Atom left = new Atom(inputIt.next(), false);
		Atom right = new Atom(inputIt.next(), false);
		Equation mainEquation = new Equation();
		mainEquation.addToLeft(left);
		mainEquation.addToRight(right);
		return mainEquation;
	}

	public Ontology createOntology(OWLOntology owlOntology) {
		if (owlOntology == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		Ontology ret = new Ontology();
		OntologyBuilder builder = new OntologyBuilder(ret);
		builder.loadOntology(owlOntology);
		return ret;
	}

	public Set<String> getCandidates() {
		return Collections.unmodifiableSet(this.candidates);
	}

	public Ontology getOntology() {
		return this.ontology;
	}

	public Translator getTranslator() {
		return this.translator;
	}

	public List<String> getUnifierList() {
		return Collections.unmodifiableList(this.unifierList);
	}

	public void loadOntology(Ontology ontology) {
		this.ontology.merge(ontology);
	}

}
