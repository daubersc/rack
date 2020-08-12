import sqlparse
import radb.ast
import re

sql = "select gender from person where age = 16"
stmt = sqlparse.parse(sql)[0]

def connect(tree, mode):
    """
    Connects the statements of a given tree.

    :param tree: The tree to extract the statements from.
    :param mode: The mode that determines the connection
    :return: The connected statement
    """
    length = len(tree)
    if (length > 1):
        first = 0
        i = first
        while (i < length - 1):
            left = tree.pop(first)
            right = tree.pop(first)
            if mode == 'relation':  # Build the cartesian Product.
                cross = radb.ast.Cross(left, right)
                tree.insert(first, cross)
            elif mode == 'and':  # Conjunction
                ands = radb.ast.ValExprBinaryOp(left, radb.ast.sym.AND, right)
                tree.insert(first, ands)
            i += 1
    return tree.pop()


def translate(statement):
    """
    This method takes a parsed SQL statement and translates canonically into
    relational algebra using the selection, projection, Cartesian Product and
    renaming operators in a bottom-up approach.
    Note that the _canonical_translation_ is required, meaning:
    - The relations have to be in the _same_ order as specified by 'from'
    - The selection is put _on_top_ of any existing Cartesian Products.
    - The projection is put _on_top_ of all, i.e. at the root of the tree.
    """
    exp_tree = []  # For the results.
    rel_tree = []  # For relations.
    sel_tree = []  # For selection.

    for token in statement:
        if token.value.lower() == "from":
            """
            The 'from' clause defines the relations, the rename of relations 
            as well as the amount of cartesian products (0,n( present where n 
            is the integer of number of relations. 
            """

            relations = statement.token_next(statement.token_index(token))[1]
            relations = [tkn for tkn in relations.tokens if
                         not (re.match("[\W]", tkn.value) or tkn.is_whitespace)]
            # Trim non relation values, i.e. ',' or whitespaces.

            existsOne = False # Boolean to break the loop on E! R.

            for identifier in relations:
                if type(identifier) == sqlparse.sql.Token:
                    """
                    If the item in the tokens list is no identifier, set to 
                    its identifier. Furthermore this only happens on exactly 
                    one relation. 
                    """
                    identifier = identifier.parent
                    existsOne = True

                relation = radb.ast.RelRef(identifier.get_real_name())
                # The actual relation's name and not the alias.

                if (identifier.has_alias()):
                    # If alias exists add rename(relation) to the tree.
                    alias = identifier.get_alias()
                    rename = radb.ast.Rename(alias, None, relation)
                    rel_tree.append(rename)
                else: # If none exists add relation to the tree.
                    rel_tree.append(relation)

                if existsOne: # If none exists break the loop and dont connect.
                    break

            exp_tree.append(connect(rel_tree, 'relation'))
            break # Do not traverse the statements further at this point.

    for token in statement:
        # Search for the 'where' clause and extract its clause

        if isinstance(token, sqlparse.sql.Where):
            token = [tkn for tkn in token if
                     isinstance(tkn, sqlparse.sql.Comparison)]

            for tkn in token:  # Extract each condition
                left = tkn.left
                right = tkn.right

                cond = radb.ast.ValExprBinaryOp(  # Build the radb statement.
                    radb.ast.AttrRef(None, left.value),
                    radb.ast.sym.EQ,
                    radb.ast.AttrRef(None, right.value)
                )
                sel_tree.append(cond)

            # Only conjuction is demanded, i.e. connect the conds with 'and'
            cond = connect(sel_tree, 'and')
            select = radb.ast.Select(cond, exp_tree.pop())
            exp_tree.append(select)
            break;

    for token in statement:
        # Search for the 'select' clause and extract its clause for projection.

        if token.value.lower() == "select":
            projection = statement.token_next(statement.token_index(token))[1]

            if projection.value.lower() == 'distinct':
                projection = statement.token_next(
                    statement.token_index(projection))[1]

            if projection.value == '*':  # if no projection necessary.
                break;
            else:
                attrs = [radb.ast.AttrRef(None, projection.value)]
                project = radb.ast.Project(attrs, exp_tree.pop())
                exp_tree.append(project)
            break;

    return exp_tree.pop()

ra = translate(stmt)
print(ra)