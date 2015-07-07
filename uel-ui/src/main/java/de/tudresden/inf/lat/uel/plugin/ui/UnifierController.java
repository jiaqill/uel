package de.tudresden.inf.lat.uel.plugin.ui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Map;
import java.util.Set;

import javax.swing.JFileChooser;

import org.semanticweb.owlapi.io.OWLRendererException;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import de.tudresden.inf.lat.uel.core.processor.UelModel;
import de.tudresden.inf.lat.uel.core.type.AtomManager;
import de.tudresden.inf.lat.uel.core.type.KRSSRenderer;

/**
 * This is the controller for the panel that shows the unifiers.
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
			try {
				getModel().computeNextUnifier();
			} catch (InterruptedException ex) {
			}
			if (getModel().getUnifierList().size() == previousSize) {
				this.allUnifiersFound = true;
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
			try {
				getModel().computeNextUnifier();
			} catch (InterruptedException ex) {
			}
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
		if (getModel().getUnifierList().size() == 0) {
			return;
		}

		JFileChooser fileChooser = new JFileChooser();
		int returnVal = fileChooser.showSaveDialog(getView());
		File file = null;
		if (returnVal == JFileChooser.APPROVE_OPTION) {
			file = fileChooser.getSelectedFile();
		}

		if (file != null) {
			try {
				String unifier = printCurrentUnifier(false);
				OntologyRenderer renderer = new OntologyRenderer();
				OWLOntology owlOntology = renderer.parseOntology(unifier);
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
				writer.write(unifier);
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

	public UelModel getModel() {
		return getView().getModel();
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

	public void setStatInfo(StatInfo info) {
		if (info == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		this.statInfo = info;
	}

	private String printCurrentUnifier(boolean shortForm) {
		AtomManager atomManager = getModel().getAtomManager();
		Set<Integer> userVariables = getModel().getPluginGoal()
				.getUserVariables();
		Set<Integer> auxVariables = getModel().getPluginGoal()
				.getAuxiliaryVariables();
		KRSSRenderer renderer = new KRSSRenderer(atomManager, userVariables,
				auxVariables, mapIdLabel);
		return renderer.printUnifier(getModel().getUnifierList().get(
				this.unifierIndex));
	}

	private void updateUnifier() {
		if (getModel().getUnifierList().size() > 0) {
			getView().getUnifier().setText(printCurrentUnifier(true));
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