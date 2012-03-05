package de.tudresden.inf.lat.uel.plugin.ui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.StringReader;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.StringTokenizer;

import javax.swing.JFileChooser;

import org.semanticweb.owlapi.io.OWLRendererException;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import de.tudresden.inf.lat.uel.plugin.processor.UelModel;
import de.tudresden.inf.lat.uel.plugin.type.AtomManager;
import de.tudresden.inf.lat.uel.type.api.Atom;
import de.tudresden.inf.lat.uel.type.api.Equation;
import de.tudresden.inf.lat.uel.type.cons.KRSSKeyword;
import de.tudresden.inf.lat.uel.type.impl.ConceptName;
import de.tudresden.inf.lat.uel.type.impl.ExistentialRestriction;

/**
 * 
 * @author Julian Mendez
 */
public class UnifierController implements ActionListener {

	private static final String actionFirst = "first";
	private static final String actionLast = "last";
	private static final String actionNext = "next";
	private static final String actionPrevious = "previous";
	private static final String actionSave = "save";
	private static final String actionShowStatInfo = "show statistic info";
	private static final String quotes = "\"";

	private boolean allUnifiersFound = false;
	private final Map<String, String> mapIdLabel;
	private StatInfo statInfo = null;
	private int unifierIndex = -1;
	private UnifierView view;

	public UnifierController(UnifierView view, Map<String, String> labels) {
		this.view = view;
		this.mapIdLabel = labels;
		init();
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		if (e == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		String cmd = e.getActionCommand();
		if (cmd.equals(actionFirst)) {
			executeActionFirst();
		} else if (cmd.equals(actionPrevious)) {
			executeActionPrevious();
		} else if (cmd.equals(actionNext)) {
			executeActionNext();
		} else if (cmd.equals(actionLast)) {
			executeActionLast();
		} else if (cmd.equals(actionSave)) {
			executeActionSave();
		} else if (cmd.equals(actionShowStatInfo)) {
			executeActionShowStatInfo();
		}
	}

	private void executeActionFirst() {
		getView().setUnifierButtons(true);

		this.unifierIndex = 0;
		updateUnifier();
	}

	private void executeActionLast() {
		while (!this.allUnifiersFound) {
			int previousSize = getModel().getUnifierList().size();
			getModel().computeNextUnifier();
			if (getModel().getUnifierList().size() == previousSize) {
				this.allUnifiersFound = true;
				this.unifierIndex = getModel().getUnifierList().size() - 1;
			}
		}
		this.unifierIndex = getModel().getUnifierList().size() - 1;
		updateUnifier();
	}

	private void executeActionNext() {
		getView().setUnifierButtons(true);

		this.unifierIndex++;
		if (this.unifierIndex >= getModel().getUnifierList().size()) {
			int previousSize = getModel().getUnifierList().size();
			getModel().computeNextUnifier();
			if (getModel().getUnifierList().size() == previousSize) {
				this.allUnifiersFound = true;
				this.unifierIndex = getModel().getUnifierList().size() - 1;
			}
		}
		updateUnifier();
	}

	private void executeActionPrevious() {
		getView().setUnifierButtons(true);

		this.unifierIndex--;
		if (this.unifierIndex < 0) {
			this.unifierIndex = 0;
		}
		updateUnifier();
	}

	private void executeActionSave() {
		JFileChooser fileChooser = new JFileChooser();
		int returnVal = fileChooser.showSaveDialog(getView());
		File file = null;
		if (returnVal == JFileChooser.APPROVE_OPTION) {
			file = fileChooser.getSelectedFile();
		}
		if (file != null) {
			try {
				String unifier = toKRSS(getModel().getUnifierList().get(
						this.unifierIndex));
				OntologyRenderer renderer = new OntologyRenderer();
				OWLOntology owlOntology = renderer.parseKRSS(unifier);
				if (file.getName().endsWith(OntologyRenderer.EXTENSION_RDF)) {
					unifier = renderer.renderRDF(owlOntology);
				} else if (file.getName().endsWith(
						OntologyRenderer.EXTENSION_OWL)) {
					unifier = renderer.renderOWL(owlOntology);
				} else if (file.getName().endsWith(
						OntologyRenderer.EXTENSION_KRSS)) {
					unifier = renderer.renderKRSS(owlOntology);
				}

				BufferedWriter writer = new BufferedWriter(new FileWriter(file));
				if (getModel().getUnifierList().size() > 0) {
					writer.write(unifier);
				}
				writer.flush();
				writer.close();
			} catch (OWLRendererException e) {
				throw new RuntimeException(e);
			} catch (OWLOntologyCreationException e) {
				throw new RuntimeException(e);
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		}
	}

	private void executeActionShowStatInfo() {
		statInfo.setInfo(getModel().getUelProcessor().getInfo());
		StatInfoController statInfoWindow = new StatInfoController(
				new StatInfoView(this.statInfo));
		statInfoWindow.open();
	}

	private String getLabel(String candidateId) {
		String ret = candidateId;
		if (candidateId.endsWith(AtomManager.UNDEF_SUFFIX)) {
			ret = candidateId.substring(0, candidateId.length()
					- AtomManager.UNDEF_SUFFIX.length());
		}

		String str = this.mapIdLabel.get(ret);
		if (str != null) {
			ret = str;
		}
		if (candidateId.endsWith(AtomManager.UNDEF_SUFFIX)) {
			ret += AtomManager.UNDEF_SUFFIX;
		}
		return ret;
	}

	public UelModel getModel() {
		return getView().getModel();
	}

	private Collection<Atom> getSetOfSubsumers(Atom atom) {
		Set<Atom> ret = new HashSet<Atom>();
		Set<Equation> equations = getModel().getUelProcessor().getUnifier()
				.getEquations();
		for (Equation equation : equations) {
			if (equation.getLeft()
					.equals(getModel().getAtomManager().getAtoms()
							.addAndGetIndex(atom))) {
				for (Integer id : equation.getRight()) {
					ret.add(getModel().getAtomManager().getAtoms().get(id));
				}
			}
		}
		return ret;
	}

	public UnifierView getView() {
		return this.view;
	}

	private void init() {
		getView().addButtonFirstListener(this, actionFirst);
		getView().addButtonPreviousListener(this, actionPrevious);
		getView().addButtonNextListener(this, actionNext);
		getView().addButtonLastListener(this, actionLast);
		getView().addButtonSaveListener(this, actionSave);
		getView().addButtonShowStatInfoListener(this, actionShowStatInfo);
	}

	/**
	 * Prints a substitution set (i.e. a set of atoms) as a conjunction of atoms
	 * in the krss format. Used in Translator.
	 * 
	 * @return the string representation of a substitution set
	 */
	public String printSetOfSubsumers(Collection<Atom> setOfSubsumers) {

		StringBuffer sbuf = new StringBuffer();

		if (setOfSubsumers.isEmpty()) {

			sbuf.append(KRSSKeyword.top);
			sbuf.append(KRSSKeyword.space);

		} else if (setOfSubsumers.size() == 1) {

			Atom atom = setOfSubsumers.iterator().next();
			sbuf.append(printSubstitution(atom));

		} else {

			sbuf.append(KRSSKeyword.open);
			sbuf.append(KRSSKeyword.and);
			sbuf.append(KRSSKeyword.space);

			for (Atom atom : setOfSubsumers) {
				sbuf.append(KRSSKeyword.space);
				sbuf.append(printSubstitution(atom));
				sbuf.append(KRSSKeyword.space);
			}

			sbuf.append(KRSSKeyword.space);
			sbuf.append(KRSSKeyword.close);
		}
		return sbuf.toString();
	}

	private String printSubstitution(Atom atom) {
		StringBuffer sbuf = new StringBuffer();
		if (atom.isExistentialRestriction()) {
			ConceptName child = ((ExistentialRestriction) atom).getChild();
			Integer conceptId = getModel().getAtomManager().getAtoms()
					.getIndex(child);
			boolean childIsUserVariable = getModel().getUelProcessor()
					.getInput().getUserVariables().contains(conceptId);

			sbuf.append(KRSSKeyword.open);
			sbuf.append(KRSSKeyword.some);
			sbuf.append(KRSSKeyword.space);
			String roleName = getModel().getAtomManager().getRoleName(
					((ExistentialRestriction) atom).getRoleId());
			sbuf.append(roleName);
			sbuf.append(KRSSKeyword.space);
			if (child.isVariable() && !childIsUserVariable) {
				sbuf.append(printSetOfSubsumers(getSetOfSubsumers(child)));
			} else {
				String childName = getModel().getAtomManager().getConceptName(
						child.getConceptNameId());
				sbuf.append(childName);
			}
			sbuf.append(KRSSKeyword.close);
		} else {
			ConceptName concept = (ConceptName) atom;
			Integer conceptId = getModel().getAtomManager().getAtoms()
					.getIndex(concept);
			String name = getModel().getAtomManager().getConceptName(conceptId);
			sbuf.append(name);
		}
		return sbuf.toString();
	}

	public void setStatInfo(StatInfo info) {
		if (info == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		this.statInfo = info;
	}

	private String showLabels(String text) {
		StringBuffer ret = new StringBuffer();
		try {
			BufferedReader reader = new BufferedReader(new StringReader(
					text.replace(KRSSKeyword.close, KRSSKeyword.space
							+ KRSSKeyword.close)));
			String line = new String();
			while (line != null) {
				line = reader.readLine();
				if (line != null) {
					StringTokenizer stok = new StringTokenizer(line);
					while (stok.hasMoreTokens()) {
						String token = stok.nextToken();
						String label = getLabel(token);
						if (label.equals(token)) {
							ret.append(token);
						} else {
							ret.append(quotes);
							ret.append(label);
							ret.append(quotes);
						}
						if (stok.hasMoreTokens()) {
							ret.append(KRSSKeyword.space);
						}
					}
				}
				ret.append(KRSSKeyword.newLine);
			}
		} catch (IOException e) {
			throw new IllegalStateException(e);
		}
		return ret.toString();
	}

	public String toKRSS(Set<Equation> set) {
		Set<Equation> unif = new HashSet<Equation>();
		unif.addAll(set);
		StringBuffer sbuf = new StringBuffer();
		for (Equation eq : set) {
			Atom leftPart = getModel().getAtomManager().getAtoms()
					.get(eq.getLeft());

			Set<Atom> right = new HashSet<Atom>();
			for (Integer atomId : eq.getRight()) {
				right.add(getModel().getAtomManager().getAtoms().get(atomId));
			}

			sbuf.append(KRSSKeyword.newLine);
			sbuf.append(KRSSKeyword.open);
			sbuf.append(KRSSKeyword.define_concept);
			sbuf.append(KRSSKeyword.space);
			Integer conceptId = getModel().getAtomManager().getAtoms()
					.getIndex(leftPart);
			String conceptName = getModel().getAtomManager().getConceptName(
					conceptId);
			sbuf.append(conceptName);
			sbuf.append(KRSSKeyword.space);

			sbuf.append(printSetOfSubsumers(right));
			sbuf.append(KRSSKeyword.space);
			sbuf.append(KRSSKeyword.close);
			sbuf.append(KRSSKeyword.space);
			sbuf.append(KRSSKeyword.newLine);
		}
		return sbuf.toString();

	}

	private void updateUnifier() {
		if (getModel().getUnifierList().size() > 0) {
			getView().getUnifier().setText(
					showLabels(toKRSS(getModel().getUnifierList().get(
							this.unifierIndex))));
		} else {
			getView().getUnifier().setText("[not unifiable]");
		}
		getView().getUnifierId().setText(
				" "
						+ (getModel().getUnifierList().isEmpty() ? 0
								: (this.unifierIndex + 1)) + " ");
		if (this.unifierIndex == 0) {
			getView().setButtonPreviousEnabled(false);
			getView().setButtonFirstEnabled(false);
		} else {
			getView().setButtonPreviousEnabled(true);
			getView().setButtonFirstEnabled(true);
		}
		if (this.allUnifiersFound
				&& this.unifierIndex >= getModel().getUnifierList().size() - 1) {
			getView().setButtonNextEnabled(false);
			getView().setButtonLastEnabled(false);
		} else {
			getView().setButtonNextEnabled(true);
			getView().setButtonLastEnabled(true);
		}
	}

}
