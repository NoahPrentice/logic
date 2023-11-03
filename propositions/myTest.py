def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator followed by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        x: Tuple[Union[Formula, None], str] = [None, 'Unexpected symbol']
        if string == '': # To avoid index errors (looking for a first character when there is none), we have to
                         # treat the case where the string is empty seperately.
            return x
        elif string[0] == 'T' or string[0] == 'F': # Otherwise, we check if the prefix is a constant, in whcih case we're done.
            x[0] = Formula(string[0])
            if len(string) > 1:
                x[1] = string[1:]
            else:
                x[1] = ''
        elif string[0] == '~' and len(string) > 1: # If the prefix is a ~, then we know we just parse everything to the right.
            rest = Formula._parse_prefix(string[1:])
            x[0] = Formula('~', rest[0])
            x[1] = rest[1]
        elif string[0] == '(' and len(string) > 1: # If the first char is (, we know we're looking for a binary operator.
            operatorList = [] # We want to know the placement of two things: 1) all closing parentheses (for later), and 2) all operators
            indexList = []
            pIndexList = []
            for i in range(len(string)):
                if string[i] == ')':
                    pIndexList.append(i)
                elif (string[i] == '&' or string[i] == '|' or string[i] == '+'):
                    operatorList.append(string[i])
                    indexList.append(i)
                elif (string[i] == '-' and string[i + 1] == '>'):
                    operatorList.append('->')
                    indexList.append(i)
                elif (string[i] == '-' and string[i + 1] == '&'):
                    operatorList.append('-&')
                elif (string[i] == '-' and string[i + 1] == '|'):
                    operatorList.append('-|')
                elif (string[i] == '<' and string[i + 1] == '-' and string[i + 2] == '>'):
                    operatorList.append('<->')
            if len(operatorList) == 0: # If no operators were found, then the parenthesis must be an error.
                return x
            operator = ''
            index = -1
            for i in range(len(operatorList)): # Otherwise, we want fo find what operator, if any, goes with the opening parenthesis.
                # We know this happens if the number of opening and closing parenthesis between the first char and the operator are equal.
                if string[1:indexList[i]].count('(') == string[1:indexList[i]].count(')'): # If we find any such case, we have our operator for the parenthesis!
                    operator = operatorList[i]
                    index = indexList[i]
                    break
            if index == -1: # If this never happens, we don't have a valid formula.
                return x
            # Now we know where our operator is, so we know where the left conjunct / left disjunct / antecedent is.
            # But we still have to find the right conjunct / right disjunct / consequent. We do that with our list of closing parentheses:
            # We loop through each closing parenthesis that follows the operator. If between the two, there are an equal number of opening and closing
            # parentheses, then we know that closing parenthesis goes with the operator and the opening parenthesis.
            pIndex = -1
            if operator == '->':
                for i in pIndexList:
                    if i < index:
                        pass
                    elif string[index + 2:i].count('(') == string[index + 2:i].count(')'):
                        pIndex = i
                        break
            elif operator == '&' or operator == '|':
                for i in pIndexList:
                    if i < index:
                            pass
                    elif string[index + 1:i].count('(') == string[index + 1:i].count(')'):
                        pIndex = i
                        break
            else:
                return x
            if pIndex == -1: # If we found no such candidate, the parentheses are not closed and so the formula is not valid.
                return x
            left = Formula._parse_prefix(string[1:index]) # Otherwise, we go ahead and parse the left and right pieces.
            if operator == '->':
                right = Formula._parse_prefix(string[index + 2:pIndex])
            else:
                right = Formula._parse_prefix(string[index + 1:pIndex])
            if left[0] is not None and right[0] is not None and left[1] == '' and right[1] == '':
                # The 4 above criteria will be met if and only if the left and right pieces were valid formulae.
                x[0] = Formula(operator, left[0], right[0])
                x[1] = string[pIndex + 1:]
            return x
        elif is_variable(string[0]): # If the first char is not ( but rather a valid variable, we make sure we return the whole thing.
            x[0] = Formula(string[0]) # We set our formula initially to the variable of the first character ('x' in 'x12').
            onlyFirstChar = True
            if len(string) == 1: # If our string has length 1 and the first character is a variable, then it's something like 'x'
                                 # in which case we are done.
                x[1] = ''
                return x
            else: # Otherwise, we need to check if the first character as a variable is really the prefix of another variable.
                for i in range(1, len(string)):
                    if is_variable(string[:i + 1]):     # If it really is the prefix of another variable,
                        x[0] = Formula(string[:i + 1])  # we change our formula to reflect that,
                        x[1] = string[i + 1:]           # and we say the rest is everything past it.
                        onlyFirstChar = False
            if onlyFirstChar: # If, in fact, the first character is the entirety of the variable, then we return it and the rest.
                x[1] = string[1:]
            return x
        return x