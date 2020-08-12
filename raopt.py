import radb.ast
import radb.parse

op_and = radb.ast.sym.AND

def rule_break_up_selections(parent):
    """
    A conjunction in a selection predicate may be broken into several nested
    selections.
    :param ra: A parsed radb statement that shall be optimized.
    :return: An optimized radb statement.
    """
    if isinstance(parent, radb.ast.RelRef):
        return parent

    child = parent.inputs[0]

    if isinstance(parent, radb.ast.Project):
        return radb.ast.Project(parent.attrs, rule_break_up_selections(child))

    if isinstance(parent, radb.ast.Rename):
        return radb.ast.Rename(parent.relname, parent.attrnames, child)

    if isinstance(parent, radb.ast.Select):

        isNested = parent.cond.op == op_and

        if not isNested:
            return parent

        relation = child
        conditions = parent.cond.inputs
        for cond in reversed(conditions):
            if cond.op == op_and:
                for sub_cond in reversed(cond.inputs):
                    relation = radb.ast.Select(sub_cond, relation)
            else:
                relation = radb.ast.Select(cond, relation)
        return relation











def concat_and_tree(root, subtree):
    if isinstance(root, radb.ast.Select):
        child = root.inputs[0]
        while isinstance(root, radb.ast.Select):
            tmp = radb.ast.Select(root.cond, child)
            root = child
            child = root.inputs[0]
        tmp.inputs[0] = subtree
        return tmp
    else:
        return subtree


def rule_push_down_selections(parent, dd):
    """
    Nested selections may swap places and a selection can be pushed down over a
    cross product if it only requires the attributes of one of the operands.
    :param ra: A parsed radb statement that shall be optimized.
    :param dd: A data dictionary that describes the relational schema.
    :return: An optimized radb statement.
    """
    # Base case: parent node is a relation.
    if isinstance(parent, radb.ast.RelRef):
        return parent

    child = parent.inputs[0]

    # Node is a projection.
    if isinstance(parent, radb.ast.Project):
        return radb.ast.Project(parent.attrs,
                                rule_push_down_selections(child, dd))

    # Node is a selection.
    if isinstance(parent, radb.ast.Select):
        leaf = get_select_leaf(parent)
        # return if chain doesnt end with cross product.
        if not isinstance(leaf, radb.ast.Cross):
            return parent
        else:
            node = parent
            selects = []

            # store all selects in a list
            while isinstance(node, radb.ast.Select):
                selects.append(node)
                node = node.inputs[0]

            i = len(selects) - 1

            while i > 0:
                node = selects[i]
                cond = node.cond
                left_cond = cond.inputs[0]
                right_cond = cond.inputs[1]

                l_tree = get_select_leaf(leaf).inputs[0]
                r_tree = get_select_leaf(leaf).inputs[1]

                # Theta selects:
                if isinstance(left_cond, radb.ast.AttrRef) \
                        == isinstance(right_cond, radb.ast.AttrRef):
                    l_attr = (left_cond.name, left_cond.rel)
                    r_attr = (right_cond.name, right_cond.rel)

                    l_is_left = is_in_subtree(l_tree, dd, l_attr)
                    r_is_right = is_in_subtree(r_tree, dd, r_attr)

                    # different sides => has to reside
                    if l_is_left == r_is_right:
                        leaf = radb.ast.Select(cond, leaf)

                    # both are left: move to left tree
                    elif l_is_left and not r_is_right:
                        l_tree = get_select_leaf(leaf).inputs[0]
                        r_tree = get_select_leaf(leaf).inputs[1]
                        l_tree = radb.ast.Select(cond, l_tree)
                        tree = radb.ast.Cross(l_tree, r_tree)

                        # Concat the nodes accordingly
                        leaf = concat_select_tree(leaf, tree)

                    # both are right: move to right tree
                    elif not l_is_left and r_is_right:
                        l_tree = get_select_leaf(leaf).inputs[0]
                        r_tree = get_select_leaf(leaf).inputs[1]
                        r_tree = radb.ast.Select(cond, r_tree)
                        tree = radb.ast.Cross(l_tree, r_tree)

                        # Concat the nodes accordingly
                        leaf = concat_select_tree(leaf, tree)

                # regular selects
                else:
                    attr = (left_cond.name, left_cond.rel, cond) \
                        if isinstance(left_cond, radb.ast.AttrRef) \
                        else (right_cond.name, right_cond.rel.cond)

                    tree = dfs_cross(get_select_leaf(leaf), dd, attr)
                    leaf = concat_select_tree(leaf, tree)

                i -= 1
            return leaf

    return parent

def concat_select_tree(root, subtree):
    if isinstance(root, radb.ast.Select):
        child = root.inputs[0]
        while isinstance(root, radb.ast.Select):
            tmp = radb.ast.Select(root.cond, child)
            root = child
            child = root.inputs[0]
        tmp.inputs[0] = subtree
        return tmp
    else:
        return subtree


def get_select_leaf(root):
    """
    get the first node that is not of type Select.
    :param root: The root of the sub tree.
    :return: The leaf node that is no Select type.
    """
    while isinstance(root, radb.ast.Select):
        root = root.inputs[0]
    return root


def is_in_rel_dict(attribute, node, dd):
    # case relation: check if attribute is in it
    if isinstance(node, radb.ast.RelRef):
        rel_dict = dd[node.rel]
        return attribute in rel_dict

    # case relation was renamed: check if attribute is in it
    elif isinstance(node, radb.ast.Rename):
        if node.relname is not None:
            rel_dict = dd[node.relname]
            return attribute in rel_dict
    else:
        return False


def dfs_cross(root, dd, attr):
    if isinstance(root, radb.ast.Rename):
        if (attr[1] == root.relname):
            return radb.ast.Select(attr[2], root)

    if isinstance(root, radb.ast.RelRef):
        if (attr[1] == root.rel) or is_in_rel_dict(attr[0], root, dd):
            return radb.ast.Select(attr[2], root)
        else:
            return root

    elif isinstance(root, radb.ast.Cross):
        l_tree = dfs_cross(root.inputs[0], dd, attr)
        r_tree = dfs_cross(root.inputs[1], dd, attr)
        return radb.ast.Cross(l_tree, r_tree)

    else:
        return root


def is_in_subtree(root, dd, attr):
    if isinstance(root, radb.ast.Select) \
            or isinstance(root, radb.ast.Rename) \
            or isinstance(root, radb.ast.Project):
        return is_in_subtree(root.inputs[0], dd, attr)
    if isinstance(root, radb.ast.RelRef):
        if (attr[1] == root.rel) or is_in_rel_dict(attr[0], root, dd):
            return True;
        else:
            return False;
    elif isinstance(root, radb.ast.Cross):
        return is_in_subtree(root.inputs[0], dd, attr) \
               or is_in_subtree(root.inputs[1], dd, attr)


def rule_merge_selections(parent):
    # base-case: Relation
    if isinstance(parent, radb.ast.RelRef):
        return parent

    child = parent.inputs[0]

    # Check for projection
    if isinstance(parent, radb.ast.Project):
        return radb.ast.Project(parent.attrs, rule_merge_selections(child))

    # Check for renames
    if isinstance(parent, radb.ast.Rename):
        rel = parent.relname
        attrs = parent.attrnames
        return radb.ast.Rename(rel, attrs, rule_merge_selections(child))

    # Base case: Selection follows selection.
    if isinstance(parent, radb.ast.Select):
        conditions = []
        cond = parent.cond

        while isinstance(child, radb.ast.Select):
            conditions.append(child.cond)
            child = child.inputs[0]

        i = 0

        while i < len(conditions):
            cond = radb.ast.ValExprBinaryOp(cond, radb.ast.sym.AND,
                                            conditions[i])
            i += 1

        return radb.ast.Select(cond, child)

    # Check for cross products.
    if isinstance(parent, radb.ast.Cross):
        other_child = parent.inputs[1]
        return radb.ast.Cross(
            rule_merge_selections(child),
            rule_merge_selections(other_child)
        )

    return parent


def rule_introduce_joins(parent):
    # base-case: Relation
    if isinstance(parent, radb.ast.RelRef):
        return parent

    child = parent.inputs[0]

    # Check for mounted projection.
    if isinstance(parent, radb.ast.Project):
        return radb.ast.Project(parent.attrs, rule_introduce_joins(child))

    # Check for renames
    if isinstance(parent, radb.ast.Rename):
        rel = parent.relname
        attrs = parent.attrnames
        return radb.ast.Rename(rel, attrs, rule_introduce_joins(child))

    # Check for theta joins
    if isinstance(parent, radb.ast.Select):
        if isinstance(child, radb.ast.Cross):
            left = child.inputs[0]
            right = child.inputs[1]
            return radb.ast.Join(rule_introduce_joins(left), parent.cond,
                                 rule_introduce_joins(right))

    # Check for cross products
    if isinstance(parent, radb.ast.Cross):
        other_child = parent.inputs[1]
        return radb.ast.Cross(rule_introduce_joins(child),
                              rule_introduce_joins(other_child))

    return parent