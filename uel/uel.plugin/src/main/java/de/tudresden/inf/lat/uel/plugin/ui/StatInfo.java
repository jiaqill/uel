package de.tudresden.inf.lat.uel.plugin.ui;

import java.util.HashMap;
import java.util.Map;

import de.tudresden.inf.lat.uel.plugin.processor.PluginGoal;
import de.tudresden.inf.lat.uel.plugin.type.AtomManager;

/**
 * 
 * @author Julian Mendez
 */
public class StatInfo {

	private static final String keyNumberOfVariables = "Number of variables";

	private Map<String, String> info;
	private final Map<String, String> mapIdLabel;
	private final PluginGoal pluginGoal;

	public StatInfo(PluginGoal g, Map<String, String> info,
			Map<String, String> labels) {
		if (g == null) {
			throw new IllegalArgumentException("Null argument.");
		}
		if (info == null) {
			throw new IllegalArgumentException("Null argument.");
		}
		if (labels == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		this.pluginGoal = g;
		setInfo(info);
		this.mapIdLabel = labels;
	}

	@Override
	public boolean equals(Object o) {
		boolean ret = (this == o);
		if (!ret && o instanceof StatInfo) {
			StatInfo other = (StatInfo) o;
			ret = this.pluginGoal.equals(other.pluginGoal)
					&& this.info.equals(other.info);

		}
		return ret;
	}

	public Map<String, String> getInfo() {
		return this.info;
	}

	public String getLabel(String id) {
		if (id == null) {
			throw new IllegalArgumentException("Null argument.");
		}

		String ret = this.mapIdLabel.get(id);

		if (ret == null) {
			if (id.endsWith(AtomManager.UNDEF_SUFFIX)) {
				String origId = id.substring(0, id.length()
						- AtomManager.UNDEF_SUFFIX.length());
				ret = this.mapIdLabel.get(origId);
				if (ret != null) {
					ret += AtomManager.UNDEF_SUFFIX;
				}
			}
		}

		if (ret == null) {
			ret = id;
		}
		return ret;
	}

	public PluginGoal getPluginGoal() {
		return this.pluginGoal;
	}

	@Override
	public int hashCode() {
		return this.pluginGoal.hashCode();
	}

	public void setInfo(Map<String, String> info) {
		this.info = new HashMap<String, String>(info);
		this.info.put(keyNumberOfVariables,
				"" + pluginGoal.getVariableSetSize());
	}

	@Override
	public String toString() {
		StringBuffer sbuf = new StringBuffer();
		sbuf.append(getPluginGoal());
		sbuf.append("\n");
		sbuf.append(getInfo());
		sbuf.append("\n");
		return sbuf.toString();
	}

}
