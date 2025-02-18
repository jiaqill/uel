package de.tudresden.inf.lat.uel.rule.rules;

// import com.sun.org.apache.xpath.internal.operations.Variable;
import de.tudresden.inf.lat.uel.rule.Assignment;
import de.tudresden.inf.lat.uel.rule.FlatConstraint;
import de.tudresden.inf.lat.uel.rule.Result;
import de.tudresden.inf.lat.uel.type.api.Atom;
import de.tudresden.inf.lat.uel.type.impl.ExistentialRestriction;

import java.util.*;


public final class TypeChoosing extends Rule<Atom> {

    public Application getFirstApplication(Atom at, Assignment assign) {
        List<Atom> typeList = assign.types.get(at);
        if (typeList == null || typeList.isEmpty()) {
            return null;
        }
        return new Application(typeList.get(0));
    }

    public Application getNextApplication(Atom at, Assignment assign, Rule.Application previous) {
        if (!(previous instanceof Application)) {
            throw new IllegalArgumentException("Expected rule application of type TypeChoosingRule.Application.");
        }
        Application appl = (Application) previous;
        List<Atom> typeList = assign.types.get(at);
        if (typeList == null || typeList.isEmpty()) {
            return null;
        }
        int index = typeList.indexOf(appl.type);
        if (index == -1 || index + 1 >= typeList.size()) {
            return null;
        }
        appl.type = typeList.get(index + 1);
        return appl;


    }

    public Result apply(Atom at, Assignment assign, Rule.Application application) {
        Application appl = (Application) application;
        //assign.types.put(at, Collections.singletonList(appl.type));
        assign.types.put(at, new LinkedList<>(Collections.singletonList(appl.type)));
        return new Result(at, application);
        /*Application appl = (Application) application;
        Result res = new Result(null, application);
        if (appl.type.isVariable()) {
            FlatConstraint newSub = new FlatConstraint(Collections.<Atom> singletonList(var), appl.type, false);
            res.getNewUnsolvedConstraints().add(newSub);
        } else if (appl.type.equals(assign.goal.getRoleGroupTypes().values())) {

        }
        return res;*/
    }

    @Override
    String shortcut() {
        return "TC";
    }

    private final class Application extends Rule.Application {

        protected Atom type;

        protected Application(Atom type) {
            this.type = type;
        }

    }

}

