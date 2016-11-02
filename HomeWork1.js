function Variable(str) {
    return {
        sign: undefined,
        name: str,
        string: str
    }
}

function Edge(l, r, sgn) {
    return {
        left: l,
        right: r,
        sign: sgn
    }
}

function negate(expr) {
    var edge;
    if (expr[0] == '!') {
        edge = Edge(negate(expr.substring(1, expr.length)), undefined, '!');
        edge.string = '!' + edge.left.string;
        return (edge);
    }
    if (expr[0] == '(') {
        return expression(expr.substring(1, expr.length - 1));
    }
    return Variable(expr);
}

function conjunct(expr) {
    var brackets = 0;
    var edge;
    for (var i = 0; i < expr.length; i++) {
        if (i == expr.length - 1) {
            return negate(expr);
        }
        switch (expr[i]) {
            case '(':
                brackets++;
                break;
            case ')':
                brackets--;
                break;
            case '&':
                if (brackets != 0) break;
                edge = Edge(conjunct(expr.substring(0, i)), negate(expr.substring(i + 1, expr.length)), '&');
                edge.string = '(' + edge.left.string + '&' + edge.right.string + ')';
                return (edge);
        }
    }
}

function disjunct(expr) {
    var brackets = 0;
    var edge;
    for (var i = 0; i < expr.length; i++) {
        if (i == expr.length - 1) {
            return conjunct(expr);
        }
        switch (expr[i]) {
            case '(':
                brackets++;
                break;
            case ')':
                brackets--;
                break;
            case '|':
                if (brackets != 0) break;
                edge = Edge(disjunct(expr.substring(0, i)), conjunct(expr.substring(i + 1, expr.length)), '|');
                edge.string = '(' + edge.left.string + '|' + edge.right.string + ')';
                return (edge);
        }
    }
    return (some);
}

function expression(expr) {
    var brackets = 0,
        edge;
    for (var i = 0; i < expr.length; i++) {
        if (i == expr.length - 1) {
            return disjunct(expr);
        }
        switch (expr[i]) {
            case '(':
                brackets++;
                break;
            case ')':
                brackets--;
                break;
            case '-':
                if (brackets != 0) break;
                edge = Edge(disjunct(expr.substring(0, i)), expression(expr.substring(i + 2, expr.length)), '->');
                edge.string = '(' + edge.left.string + '->' + edge.right.string + ')';
                return edge;
        }
    }
}

var schemeAx = [function(t) {
    if (t.sign == '->' && t.right.sign == '->')
        return (t.left.string == t.right.right.string);
}, function(t) {
    if (t.sign == '->' && t.left.sign == '->' && t.right.sign == '->' && t.right.left.sign == '->' && t.right.right.sign == '->' && t.right.left.right.sign == '->')
        return (t.left.left.string == t.right.left.left.string) && (t.left.left.string == t.right.right.left.string) &&
            (t.left.right.string == t.right.left.right.left.string) && (t.right.left.right.right.string == t.right.right.right.string);
}, function(t) {
    if (t.sign == '->' && t.right.sign == '->' && t.right.right.sign == '&') {
        return ((t.left.string == t.right.right.left.string) && (t.right.left.string == t.right.right.right.string));
    }
}, function(t) {
    if (t.sign == '->' && t.left.sign == '&') {
        return (t.left.left.string == t.right.string);
    }
}, function(t) {
    if (t.sign == '->' && t.left.sign == '&') {
        return (t.left.right.string == t.right.string);
    }
}, function(t) {
    if (t.sign == '->' && t.right.sign == '|') {
        return (t.left.string == t.right.left.string);
    }
}, function(t) {
    if (t.sign == '->' && t.right.sign == '|') {
        return (t.left.string == t.right.right.string);
    }
}, function(t) {
    if (t.sign == '->' && t.left.sign == '->' && t.right.sign == '->' && t.right.left.sign == '->' && t.right.right.sign == '->' && t.right.right.left.sign == '|') {
        return (t.left.left.string == t.right.right.left.left.string) && (t.left.right.string == t.right.left.right.string) &&
            (t.left.right.string == t.right.right.right.string) && (t.right.left.left.string == t.right.right.left.right.string);
    }
}, function(t) {
    if (t.sign == '->' && t.left.sign == '->' && t.right.sign == '->' && t.right.left.sign == '->' && t.right.right.sign == '!' && t.right.left.right.sign == '!') {
        return (t.left.left.string == t.right.left.left.string) && (t.left.left.string == t.right.right.left.string) &&
            (t.left.right.string == t.right.left.right.left.string);
    }
}, function(t) {
    if (t.sign == '->' && t.left.sign == '!' && t.left.left.sign == '!') {
        return (t.right.string == t.left.left.left.string);
    }
}]

function checkAxeom(tree) {
    for (var i = 0; i < 10; i++) {
        if (schemeAx[i](tree)) {
            return (i + 1);
        }
    }
    return (-1);
}

var axeoms = [];

var fs = require('fs');
var input = fs.readFileSync('input.txt', 'utf8');

var strings = input.split('\n'),
    proof = [];
for (var i = 0; i < strings.length; i++) {
    strings[i] = strings[i].replace(new RegExp("[ \r\t]", 'g'), '');
    if (strings[i].length > 0) {
        proof.push(strings[i]);
    }
}
var header = proof.shift();
var implic = [];
header = header.split('|-');
header = header[0].split(',');

function parseAxeom(t) {
    if (typeof(implic[t.right.string]) == 'undefined') {
        var g = [];
        g.push(i);
        implic[t.right.string] = g;
    } else {
        implic[t.right.string].push(i);
    }
}
var axeoms = [];
for (var i = 0; i < header.length; i++) {
    if (header[i].length > 0)
        axeoms.push(expression(header[i]));
}
var usedAxeoms = [],
    axeomTrees = [];
var ans = '';
for (var i = 0; i < proof.length; i++) {
    var gotAns = false;
    var tree = expression(proof[i]);
    axeomTrees[i] = tree;
    var isAxeoma = checkAxeom(tree);
    if (tree.sign == '->')
        parseAxeom(tree);
    if (typeof(usedAxeoms[tree.string]) == 'undefined') {
        var g = [];
        g.push(i);
        usedAxeoms[tree.string] = g;
    }
    if (isAxeoma > 0) {
        ans += '(' + (i + 1) + ') ' + proof[i] + " (Сх. акс. " + isAxeoma + ")\n";
        continue;
    }
    for (var j = 0; j < axeoms.length; j++) {
        if (axeoms[j].string == tree.string) {
            ans += '(' + (i + 1) + ') ' + proof[i] + " (Предп. " + (j + 1) + ")\n";
            gotAns = true;
            break;
        }
    }
    if (typeof(implic[tree.string]) != 'undefined')
        for (var j = 0; j < implic[tree.string].length; j++) {
            var ind = implic[tree.string][j];
            var s = axeomTrees[ind];
            if (typeof(usedAxeoms[s.left.string]) != 'undefined') {
                ans += '(' + (i + 1) + ') ' + proof[i] + ' ' + "(M.P. " + (usedAxeoms[s.left.string][0] + 1) + ', ' + (ind + 1) + ')\n';
                gotAns = true;
                break;
            }
        }
    if (!gotAns)
        ans += '(' + (i + 1) + ') ' + proof[i] + " (Не доказано)\n";
}
fs.writeFileSync('output.txt', ans);