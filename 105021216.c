#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <stdlib.h>

/*
Something like Python
>> y = 2
>> z = 2
>> x = 3*y + 4/(2*z)

*/

/*
the only type: integer
everything is an expression

    statement 	:= END | expr END
    expr      	:= term expr_tail
    expr_tail 	:= ADD_SUB_AND_OR_XOR term expr_tail | NiL
    term      	:= factor term_tail
    term_tail 	:= MUL_DIV factor term_tail|NiL
    factor    	:= INT | ADD_SUB INT | ADD_SUB ID | ID ASSIGN expr| ID | LPAREN expr RPAREN

*/

#define MAXLEN 256
#define TBLSIZE 64


typedef enum { MISPAREN, NOTNUMID, NOTFOUND, RUNOUT, DIVIDEDBYZERO, NOTQUALITY
} ErrorType;
typedef enum {
    UNKNOWN, END, INT, ID, ORANDXOR, ADDSUB, MULDIV, ASSIGN,
    LPAREN, RPAREN, ENDFILE
} TokenSet;

typedef struct {
    char name[MAXLEN];
    int val;
} Symbol;

Symbol table[TBLSIZE];

typedef struct _Node {
    char lexeme[MAXLEN];
    TokenSet data;
    int val;
    struct _Node* left, * right;
} BTNode;

TokenSet lookahead = UNKNOWN;
char lexeme[MAXLEN];
BTNode* forest[1000];
char forestVarName[1000][256];
//r3 as t0, r4 as t1
int stackPointer = 4;
int forestSize = 0;
BTNode* processedForest[1000];
int processedForestSize = 0;
int A[3] = { 0,0,0 };
BTNode* xyzForest[3];


BTNode* copyTree(BTNode*);

BTNode* factor(void);
BTNode* term(void);
BTNode* term_tail(BTNode*);
BTNode* expr(void);
BTNode* expr_tail(BTNode*);
void statement(void);
char* getLexeme(void);
TokenSet getToken(void);
void advance(void);
void error(ErrorType);
int match(TokenSet);
int evaluateTree(BTNode*,int);
void printPrefix(BTNode*);
void freeTree(BTNode*);
BTNode* makeNode(TokenSet, const char*);
int getval(void);
int setval(char*, int);
void simplifyTree(BTNode*);
void  simplifyForest(void);
void alloc(void);
void spare(void);
void check(BTNode* root);
int isOP(TokenSet);
int isGlobalVar(char*);
int isINTZERO(BTNode*);
int doesListInForestVarName(char*);
void substituteTree(BTNode**, int);
int getGlobalVarNum(char* );
void evaluateXYZForest(void);
int isCommutative(char* );
BTNode** findChangeableID(char*, BTNode*);
BTNode** findChangeableINT(char*, BTNode*);
void commuteSimplify(BTNode*);

int main(void)
{
    
    //freopen( "input.txt" , "r" , stdin );
    //freopen( "output.txt" , "w" , stdout ) ;
   
    while (!feof(stdin)) {
        statement();
    }
    evaluateXYZForest();
    printf("EXIT 0");
    return 0;
}

int sbcount = 0;
int getval(void)
{
    int i, retval, found;

    if (match(INT)) {
        retval = atoi(getLexeme());
    }
    else if (match(ID)) {
        i = 0; found = 0; retval = 0;
        while (i < sbcount && !found) {
            if (strcmp(getLexeme(), table[i].name) == 0) {
                retval = table[i].val;
                found = 1;
                break;
            }
            else {
                i++;
            }
        }
        if (!found) {
            if (sbcount < TBLSIZE) {
                strcpy(table[sbcount].name, getLexeme());
                table[sbcount].val = 0;
                sbcount++;
            }
            else {
                error(RUNOUT);
            }
        }
    }
    return retval;
}
int setval(char* str, int val)
{
    int i, retval;
    i = 0;
    while (i < sbcount) {
        if (strcmp(str, table[i].name) == 0) {
            table[i].val = val;
            retval = val;
            break;
        }
        else {
            i++;
        }
    }
    return retval;
}

int evaluateTree(BTNode* root, int desireAddress)
{
    int retval = 0, lv=0, rv=0;
    if (root != NULL)
    {
        switch (root->data)
        {
        case ID:
            if (A[0] == 0 && strcmp(root->lexeme, "x") == 0) {
                printf("MOV r0 [0]\n");
                A[0]=1;
            }
            else if (A[1] == 0 && strcmp(root->lexeme, "y") == 0) {
                printf("MOV r1 [4]\n");
                A[1] = 1;
            }
            else if (A[2] == 0 && strcmp(root->lexeme, "z") == 0) {
                printf("MOV r2 [8]\n");
                A[2] = 1;
            }
        case INT:
            retval = root->val;
            break;
        case ASSIGN:
        case ADDSUB:
        case MULDIV:
        case ORANDXOR:
            if (strcmp(root->lexeme, "=") != 0) {
                char op[] = "ADD";
                switch (root->lexeme[0]) {
                case '+':
                    strcpy(op, "ADD");
                    break;
                case '-':
                    strcpy(op, "SUB");
                    break;
                case '*':
                    strcpy(op, "MUL");
                    break;
                case '/':
                    strcpy(op, "DIV");
                    break;
                case '|':
                    strcpy(op, "OR");
                    break;
                case '&':
                    strcpy(op, "AND");
                    break;
                case '^':
                    strcpy(op, "XOR");
                    break;
                }
                if (isOP(root->left->data) && isOP(root->right->data)) {
                    alloc();
                    int sp1 = stackPointer;
                    evaluateTree(root->left, sp1);
                    if (desireAddress < 8) {
                        int tempReg = desireAddress == 4 ? 3:4;
                        evaluateTree(root->right, desireAddress);

                        if (sp1 < 8) printf("%s r%d r%d\n", op,desireAddress, sp1);
                        else {
                            printf("MOV r%d [%d]\n", tempReg, 4 * (sp1 - 8));
                            printf("%s r%d r%d\n",op, desireAddress, tempReg);
                        }

                    }
                    else {
                        evaluateTree(root->right, 3);
                        if (sp1 < 8) printf("%s r3 r%d\n",op, sp1);
                        else {
                            printf("MOV r4 [%d]\n", 4 * (sp1 - 8));
                            printf("%s r3 r4\n",op);
                        }
                        printf("MOV [%d] r3\n", 4 * (desireAddress - 8));
                    }
                    spare();
                }//TODO abelian
                else if ((isOP(root->right->data) && root->left->data == INT)||
                         (isOP(root->left->data) && root->right->data == INT)) {
                    BTNode* OPNode = isOP(root->right->data) ? root->right : root->left;
                    BTNode* INTNode = (root->right->data) == INT ? root->right : root->left;


                    int intval = evaluateTree(INTNode, -1);

                    if (desireAddress<8) {
                        int tempReg = desireAddress == 3 ? 4 : 3;
                        if (isCommutative(op) || root->right->data == INT) {
                            int opval = evaluateTree(OPNode, desireAddress);
                            printf("MOV r%d %d\n", tempReg, intval);
                            printf("%s r%d r%d\n",op, desireAddress, tempReg);
                        }
                        else {
                            int opval = evaluateTree(OPNode, tempReg);
                            printf("MOV r%d %d\n", desireAddress, intval);
                            printf("%s r%d r%d\n", op, desireAddress, tempReg);
                        }

                    }
                    else {


                        if (isCommutative(op) || root->right->data == INT) {
                            int opval = evaluateTree(OPNode, 3);
                            printf("MOV r%d %d\n", 4, intval);
                            printf("%s r3 r4\n",op);
                            printf("MOV [%d] r3\n", 4 * (desireAddress - 8));
                        }
                        else {
                            int opval = evaluateTree(OPNode, 4);
                            printf("MOV r%d %d\n", 3, intval);
                            printf("%s r3 r4\n", op);
                            printf("MOV [%d] r3\n", 4 * (desireAddress - 8));
                        }

                    }

                }
                else if ((isOP(root->right->data) && root->left->data == ID) ||
                         (isOP(root->left->data) && root->right->data == ID)) {
                    BTNode* OPNode = isOP(root->right->data) ? root->right : root->left;
                    BTNode* IDNode = (root->right->data) == ID ? root->right : root->left;
                    int idval = evaluateTree(IDNode, -1);


                    int addressNum = getGlobalVarNum(IDNode->lexeme);
                    if (addressNum == desireAddress) {
                        int opval = evaluateTree(OPNode, 3);
                        if (isCommutative(op) || root->left->data == ID) {
                            printf("%s r%d r%d\n", op, desireAddress, 3);
                        }
                        else {
                            printf("%s r%d r%d\n", op, 3, addressNum);
                            printf("MOV r%d r%d\n", desireAddress, 3);
                        }
                    }
                    else if (desireAddress < 8) {
                        int opval = evaluateTree(OPNode, desireAddress);
                        if (isCommutative(op) || root->right->data == ID) {
                            printf("%s r%d r%d\n",op, desireAddress, addressNum);
                        }
                        else {
                            int tempReg = desireAddress == 3 ? 4 : 3;
                            printf("MOV r%d r%d\n",tempReg , addressNum);
                            printf("%s r%d r%d\n", op, tempReg, desireAddress);
                            printf("MOV r%d r%d\n", desireAddress, tempReg);
                        }
                    }
                    else {
                        int opval = evaluateTree(OPNode, 3);
                        if (isCommutative(op) || root->right->data == ID) {
                            printf("%s r%d r%d\n",op, 3, addressNum);
                            printf("MOV [%d] r%d\n", 4 * (desireAddress - 8), 3);
                        }
                        else {
                            printf("MOV r%d r%d\n", 4, addressNum);
                            printf("%s r%d r%d\n", op, 4, 3);
                            printf("MOV [%d] r%d\n", 4 * (desireAddress - 8), 4);
                        }
                    }
                }
                else if ((root->right->data == INT && root->left->data == ID) ||
                        (root->right->data == ID && root->left->data == INT)) {
                    lv = evaluateTree(root->left, -1);
                    rv = evaluateTree(root->right, -1);
                    int value = root->right->data == INT ? root->right->val : root->left->val;
                    int addressNum = root->right->data == ID ? getGlobalVarNum(root->right->lexeme) : getGlobalVarNum(root->left->lexeme);
        
                    if (addressNum == desireAddress) {
                        if (isCommutative(op) || root->left->data == ID) {
                            printf("MOV r%d %d\n", 3, value);
                            printf("%s r%d r%d\n",op, desireAddress, 3);
                        }
                        else {
                            printf("MOV r%d %d\n", 3, value);
                            printf("%s r%d r%d\n", op, 3, desireAddress);
                            printf("MOV r%d r%d\n", desireAddress, 3);
                        }
                    }
                    else if (desireAddress < 8) {
                        if (isCommutative(op) || root->left->data == INT) {
                            printf("MOV r%d %d\n", desireAddress, value);
                            printf("%s r%d r%d\n",op, desireAddress, addressNum);
                        }
                        else {
                            int tempReg = desireAddress == 3 ? 4 : 3;
                            printf("MOV r%d r%d\n", desireAddress, addressNum);
                            printf("MOV r%d %d\n", tempReg, value);
                            printf("%s r%d r%d\n", op, desireAddress, tempReg);
                        }
                    }
                    else {
                        if (isCommutative(op) || root->left->data == INT) {
                            printf("MOV r%d %d\n", 3, value);
                            printf("%s r%d r%d\n",op, 3, addressNum);
                            printf("MOV [%d] r%d\n", 4 * (desireAddress - 8), 3);
                        }
                        else {
                            printf("MOV r%d %d\n", 3, value);
                            printf("MOV r%d r%d\n", 4, addressNum);
                            printf("%s r%d r%d\n",op, 4, 3);
                            printf("MOV [%d] r%d\n", 4 * (desireAddress - 8), 3);
                        }
                    }
                }
                else if (root->right->data == ID && root->left->data == ID) {
                    lv = evaluateTree(root->left,-1);
                    rv = evaluateTree(root->right,-1);
                    int lAddressNum = getGlobalVarNum(root->left->lexeme);
                    int rAddressNum = getGlobalVarNum(root->right->lexeme);
                    if ( lAddressNum == desireAddress ) {
                        printf("%s r%d r%d\n",op , desireAddress, rAddressNum);
                    }
                    else if(rAddressNum == desireAddress){
                        if (isCommutative(op)) {
                            printf("%s r%d r%d\n", op, desireAddress, lAddressNum);
                        }
                        else {
                            printf("MOV r%d r%d\n",  3, lAddressNum);
                            printf("%s r%d r%d\n", op, 3, rAddressNum);
                            printf("MOV r%d r%d\n", desireAddress, 3);
                        }

                    }
                    else if (desireAddress < 8) {
                        printf("MOV r%d r%d\n", desireAddress, lAddressNum);
                        printf("%s r%d r%d\n",op, desireAddress, rAddressNum);
                    }
                    else {
                        printf("MOV r%d r%d\n", 3, lAddressNum);
                        printf("%s r%d r%d\n",op, 3, rAddressNum);
                        printf("MOV [%d] r%d\n", 4*(desireAddress-8), 3);
                    }
                }
            }
            else if (strcmp(root->lexeme, "=") == 0)
                if (root->right->data == INT) {
                    rv = root->right->val;
                    printf("MOV r%d %d\n", getGlobalVarNum(root->left->lexeme),rv);
                }
                else if (isOP(root->right->data)) {
                    rv = evaluateTree(root->right, getGlobalVarNum(root->left->lexeme));
                }
                //TODO improve
                else if( root->right->data == ID ) {
                    printf("MOV r%d [%d]\n", getGlobalVarNum(root->left->lexeme), 4*getGlobalVarNum(root->right->lexeme) );
                }
                //retval = setval(root->left->lexeme, rv);
            break;
        default:
            retval = 0;
        }
    }
    return retval;
}


/* print a tree by pre-order. */
void printPrefix(BTNode* root)
{
    if (root != NULL)
    {
        printf("%s ", root->lexeme);
        printPrefix(root->left);
        printPrefix(root->right);
    }
}


/* create a node without any child.*/
BTNode* makeNode(TokenSet tok, const char* lexe) {
    BTNode* node = (BTNode*)malloc(sizeof(BTNode));
    strcpy(node->lexeme, lexe);
    node->data = tok;
    node->val = 0;
    node->left = NULL;
    node->right = NULL;
    return node;
}

TokenSet getToken(void)
{
    int i;
    char c;

    while ((c = fgetc(stdin)) == ' ' || c == '\t');  // ©¿²¤ªÅ¥Õ¦r¤¸

    if (isdigit(c)) {
        lexeme[0] = c;
        c = fgetc(stdin);
        i = 1;
        while (isdigit(c) && i < MAXLEN) {
            lexeme[i] = c;
            ++i;
            c = fgetc(stdin);
        }
        ungetc(c, stdin);
        lexeme[i] = '\0';
        return INT;
    }
    else if (c == '+' || c == '-') {
        lexeme[0] = c;
        lexeme[1] = '\0';
        return ADDSUB;
    }
    else if (c == '|' || c == '&' || c == '^') {
        lexeme[0] = c;
        lexeme[1] = '\0';
        return ORANDXOR;
    }
    else if (c == '*' || c == '/') {
        lexeme[0] = c;
        lexeme[1] = '\0';
        return MULDIV;
    }
    else if (c == '\n') {
        lexeme[0] = '\0';
        return END;
    }
    else if (c == '=') {
        strcpy(lexeme, "=");
        return ASSIGN;
    }
    else if (c == '(') {
        strcpy(lexeme, "(");
        return LPAREN;
    }
    else if (c == ')') {
        strcpy(lexeme, ")");
        return RPAREN;
    }
    else if (isalpha(c) || c == '_') {
        lexeme[0] = c;
        c = fgetc(stdin);
        i = 1;
        while (isalpha(c) || isdigit(c) || c == '_') {
            lexeme[i] = c;
            ++i;
            c = fgetc(stdin);
        }
        ungetc(c, stdin);
        lexeme[i] = '\0';
        return ID;
    }
    else if (c == EOF) {
        return ENDFILE;
    }
    else {
        return UNKNOWN;
    }
}

/* factor := INT | ADD_SUB INT | ADD_SUB ID | ID ASSIGN expr| ID | LPAREN expr RPAREN */

BTNode* factor(void)
{
    BTNode* retp = NULL;
    char tmpstr[MAXLEN];

    if (match(INT)) {
        retp = makeNode(INT, getLexeme());
        retp->val = getval();
        advance();
    }
    else if (match(ID)) {
        BTNode* left = makeNode(ID, getLexeme());
        left->val = getval();
        strcpy(tmpstr, getLexeme());
        advance();
        if (match(ASSIGN)) {
            retp = makeNode(ASSIGN, getLexeme());
            advance();
            retp->right = expr();
            retp->left = left;
        }
        else {
            retp = left;
        }
    }
    else if (match(ADDSUB)) {
        strcpy(tmpstr, getLexeme());
        advance();
        if (match(ID) || match(INT)) {
            retp = makeNode(ADDSUB, tmpstr);
            if (match(ID))
                retp->right = makeNode(ID, getLexeme());
            else
                retp->right = makeNode(INT, getLexeme());
            retp->right->val = getval();
            retp->left = makeNode(INT, "0");
            retp->left->val = 0;
            advance();
        }
        else {
            error(NOTNUMID);
        }
    }
    else if (match(ORANDXOR)) {


    }
    else if (match(LPAREN)) {
        advance();
        retp = expr();
        if (match(RPAREN)) {
            advance();
        }
        else {
            error(MISPAREN);
        }
    }
    else {
        error(NOTNUMID);
    }
    return retp;
}

/* term := factor term_tail */
BTNode* term(void)
{
    BTNode* node;

    node = factor();

    return term_tail(node);
}

/* term_tail := MUL_DIV factor term_tail|NiL */
BTNode* term_tail(BTNode* left)
{
    BTNode* node;

    if (match(MULDIV)) {
        node = makeNode(MULDIV, getLexeme());
        advance();

        node->left = left;
        node->right = factor();

        return term_tail(node);
    }
    else
        return left;
}

/* expr := term expr_tail */
BTNode* expr(void)
{
    BTNode* node;

    node = term();

    return expr_tail(node);
}

/* expr_tail := ADD_SUB_AND_OR_XOR term expr_tail | NiL */
BTNode* expr_tail(BTNode* left)
{
    BTNode* node;

    if (match(ADDSUB)) {
        node = makeNode(ADDSUB, getLexeme());
        advance();

        node->left = left;
        node->right = term();

        return expr_tail(node);
    }
    else if (match(ORANDXOR)) {
        node = makeNode(ORANDXOR, getLexeme());
        advance();

        node->left = left;
        node->right = term();

        return expr_tail(node);
    }
    else
        return left;
}

void advance(void)
{
    lookahead = getToken();
}

int match(TokenSet token)
{
    if (lookahead == UNKNOWN) advance();
    return token == lookahead;
}

char* getLexeme(void)
{
    return lexeme;
}

/* statement := END | expr END */

void statement(void)
{
    BTNode* retp;

    if (match(ENDFILE)) {

        exit(0);

    }
    else if (match(END)) {

        advance();

    }
    else {

        retp = expr();
        forest[forestSize++] = retp;
        strcpy(forestVarName[forestSize - 1], retp->left->lexeme);
        simplifyTree(retp);
        check(NULL);
        simplifyForest();

        if (match(END)) {

            //printf("%d\n", k);
            //freeTree(retp);

            //printf(">> ");
            advance();
        }

    }
}
void error(ErrorType errorNum)
{
    printf("EXIT 1"); exit(0);
    switch (errorNum) {
    case MISPAREN:
        fprintf(stderr, "Mismatched parenthesis\n");
        break;
    case NOTNUMID:
        fprintf(stderr, "Number or identifier expected\n");
        break;
    case NOTFOUND:
        fprintf(stderr, "%s not defined\n", getLexeme());
        break;
    case RUNOUT:
        fprintf(stderr, "Out of memory\n");
    case DIVIDEDBYZERO:
        fprintf(stderr, "divided by zero\n");
    case NOTQUALITY:
        fprintf(stderr, "not an expression\n");
    }
    exit(0);
}
/* clean a tree.*/
void freeTree(BTNode* root) {
    if (root != NULL) {
        freeTree(root->left);
        freeTree(root->right);
        free(root);
    }
}
int isOP(TokenSet data) {
    return (data == ADDSUB || data == MULDIV || data == ORANDXOR);
}
// 
void simplifyTree(BTNode* root) {
    if (root->data == ASSIGN) {
        simplifyTree(root->left);
        simplifyTree(root->right);
    }
    else if (isOP(root->data)) {
        simplifyTree(root->left);
        simplifyTree(root->right);
        if (root->left->data == INT && root->right->data == INT) {
            int lv = root->left->val;
            int rv = root->right->val;
            int retval;
            if (strcmp(root->lexeme, "+") == 0)
                retval = lv + rv;
            else if (strcmp(root->lexeme, "-") == 0)
                retval = lv - rv;
            else if (strcmp(root->lexeme, "*") == 0)
                retval = lv * rv;
            else if (strcmp(root->lexeme, "/") == 0) {
                if (rv == 0) error(DIVIDEDBYZERO);
                retval = lv / rv;  
            }
            else if (strcmp(root->lexeme, "|") == 0) {
                retval = lv | rv;
            }
            else if (strcmp(root->lexeme, "&") == 0) {
                retval = lv & rv;
            }
            else if (strcmp(root->lexeme, "^") == 0) {
                retval = lv ^ rv;
            }
            free(root->left);
            free(root->right);
            root->data = INT;
            sprintf(root->lexeme, "%d", retval);
            root->left = NULL;
            root->right = NULL;
            root->val = retval;
            
        }
        else if (isINTZERO(root->left) || isINTZERO(root->right)) {


            if (strcmp(root->lexeme, "*") == 0 || strcmp(root->lexeme, "&") == 0) {
                free(root->left);
                free(root->right);
                root->data = INT;
                sprintf(root->lexeme, "%d", 0);
                root->left = NULL;
                root->right = NULL;
                root->val = 0;
            }
            else if (strcmp(root->lexeme, "/") == 0 && isINTZERO(root->left)) {
                free(root->left);
                free(root->right);
                root->data = INT;
                sprintf(root->lexeme, "%d", 0);
                root->left = NULL;
                root->right = NULL;
                root->val = 0;
            }
            else if (strcmp(root->lexeme, "/") == 0 && isINTZERO(root->right)) 
                error(DIVIDEDBYZERO);
            else if ( strcmp(root->lexeme, "+") == 0  || strcmp(root->lexeme, "|") == 0 || strcmp(root->lexeme, "^") == 0) {
                BTNode* node = isINTZERO(root->left) ? root->right : root->left;
                BTNode* zeroNode = isINTZERO(root->left) ? root->left : root->right;
                free(zeroNode);
                root->data = node->data;
                strcpy(root->lexeme, node->lexeme);

                root->left = node->left;
                root->right = node->right;
                root->val = node->val;
                free(node);
            }
            else if (strcmp(root->lexeme, "-") == 0 && isINTZERO(root->right)) {
                BTNode* node = root->left;
                BTNode* zeroNode = root->right;
                free(zeroNode);
                root->data = node->data;
                strcpy(root->lexeme, node->lexeme);

                root->left = node->left;
                root->right = node->right;
                root->val = node->val;
                free(node);
            }

            
        }
        else if(root->left->data == ID && root->right->data == ID){
            if (strcmp(root->lexeme, "-") == 0 || strcmp(root->lexeme, "^")==0) {
                if (strcmp(root->left->lexeme, root->right->lexeme) == 0) {
                    free(root->left);
                    free(root->right);
                    root->data = INT;
                    sprintf(root->lexeme, "%d", 0);
                    root->left = NULL;
                    root->right = NULL;
                    root->val = 0;
                }
            }
            else if (strcmp(root->lexeme, "&") == 0 || strcmp(root->lexeme, "|") == 0) {
                if (strcmp(root->left->lexeme, root->right->lexeme) == 0) {
                    root->data = ID;
                    sprintf(root->lexeme, "%s", root->left->lexeme);
                    free(root->left);
                    free(root->right);
                    root->left = NULL;
                    root->right = NULL;
                    root->val = 0;

                }
            }
        }

    }
    
}
// substitute local variables in tree (root) with i-th forest tree
void substituteTree(BTNode** root, int i) {
    if (root == NULL) return;
    if ((*root) == NULL) return;
    if ((*root)->data != ASSIGN &&(*root)->left != NULL) substituteTree(&((*root)->left),i);
    if ((*root)->right != NULL) substituteTree(&((*root)->right), i);
    //if ((*root)->data == ID && !isGlobalVar((*root)->lexeme) && strcmp(forestVarName[i], (*root)->lexeme)==0) {
    if ((*root)->data == ID && strcmp(forestVarName[i], (*root)->lexeme) == 0) {
        free(*root);
        *root = copyTree( forest[i]->right);
        //*root = forest[i]->right;
    }
}
// substitute local variables;
void simplifyForest(void) {
    if (isGlobalVar(forestVarName[forestSize - 1])) {
        for (int i = forestSize - 2; i >= 0; i--) {
            //traverse forest[forestTop-1] and substitute local variables.
            substituteTree(&(forest[forestSize - 1]), i);
        }

        simplifyTree(forest[forestSize - 1]);
        commuteSimplify(forest[forestSize - 1]);
        //printPrefix(forest[forestSize - 1]); printf("\n");
        processedForest[processedForestSize++] = forest[forestSize - 1];
        if (strcmp(forest[forestSize - 1]->left->lexeme, "x") == 0) xyzForest[0] = forest[forestSize - 1];
        if (strcmp(forest[forestSize - 1]->left->lexeme, "y") == 0) xyzForest[1] = forest[forestSize - 1];
        if (strcmp(forest[forestSize - 1]->left->lexeme, "z") == 0) xyzForest[2] = forest[forestSize - 1];




        return;
    }
}
void evaluateXYZForest(void) {
    for (int i = 0; i < 3; i++) {
        evaluateTree(xyzForest[i],-1);
        if (xyzForest[i] != NULL)  A[i] = 1;
    }

    for (int i = 0; i < 3; i++) {
        if (A[i] == 0) {
            printf("MOV r%d [%d]\n", i, 4 * i);
        }
    }

}
void alloc(void) {
    stackPointer++;
    if (stackPointer == 8) stackPointer = 11;
}
void spare(void) {
    stackPointer--;
    if (stackPointer == 10) stackPointer = 7;
}
void check(BTNode *root) {
    if (forest[forestSize-1]->data != ASSIGN) error(NOTQUALITY);
    else if (root == NULL)check(forest[forestSize - 1]->right);
    else {
        if (root->data == ASSIGN) error(NOTQUALITY);
        if (!doesListInForestVarName(root->lexeme) && !isGlobalVar(root->lexeme) && root->data == ID) {
            error(NOTFOUND);
        }
        else {
            if (root->left != NULL ) check(root->left);
            if (root->right != NULL) check(root->right);
        }
    }


}
int isGlobalVar(char* varName) {
    return (strcmp(varName, "x") == 0 || strcmp(varName, "y") == 0 || strcmp(varName, "z") == 0);
}
int isINTZERO(BTNode* root) {
    return (root->data == INT && root->val == 0);
}
int doesListInForestVarName(char* varName) {
    for (int i = 0; i < forestSize-1; i++) {
        if (strcmp(forestVarName[i], varName) == 0) return 1;
    }
    return 0;
}
int getGlobalVarNum(char* varName) {
    if (varName[1] == '\0') return varName[0] - 'x';
}
int isCommutative(char *op) {
    return !((strcmp(op, "SUB") == 0) || (strcmp(op, "DIV") == 0) || (strcmp(op, "/") == 0) || (strcmp(op, "-") == 0));
}
BTNode* copyTree(BTNode* root) {
    if (root == NULL) return NULL;
    else {
        BTNode* node = (BTNode*)malloc(sizeof(BTNode));
        node->data = root->data;
        strcpy(node->lexeme, root->lexeme);
        node->left = copyTree(root->left);
        node->right = copyTree(root->right);
        node->val = root->val;
        return node;
    }

}

// find a pair OP whose children are ID and INT and all operators in the path from root to the OP node are the same.
// OP must be commutative
BTNode** findChangeableID(char* op, BTNode* root) {
    if (root == NULL) return NULL;
    if (isCommutative(root->lexeme) && strcmp(root->lexeme, op) == 0) {
        if ((root->left->data == INT && root->right->data == ID)||
            (root->left->data == ID && root->right->data == INT)){
            return (root->left->data == ID ? &(root->left) : &(root->right));
        }
        BTNode** ln = findChangeableID(op, root->left);
        BTNode** rn = findChangeableID(op, root->left);
        return ln == NULL ? rn : ln;
    }
    return NULL;
}
BTNode** findChangeableINT(char* op, BTNode* root) {
    if (root == NULL) return NULL;
    if (isCommutative(root->lexeme) && strcmp(root->lexeme, op) == 0) {
        if ((root->left->data == INT && root->right->data != ID) ||
            (root->left->data != ID && root->right->data == INT)) {
            return (root->left->data == INT ? &(root->left) : &(root->right));
        }
        BTNode** ln = findChangeableINT(op, root->left);
        BTNode** rn = findChangeableINT(op, root->left);
        return ln == NULL ? rn : ln;
    }
    return NULL;
}
void commuteSimplify(BTNode *root) {
    if (root == NULL) return;
    if (isCommutative(root->lexeme) && isOP(root->data)) {
        char op[] = "+";
        strcpy(op, root->lexeme);

        while (1) {

            BTNode** lID = findChangeableID(op, root->left);
            BTNode** rINT = findChangeableINT(op, root->right);
            if (root->right->data == INT) rINT = &(root->right);
            if ((lID != NULL && rINT != NULL)) {
                BTNode* temp = *lID;
                *lID = *rINT;
                *rINT = temp;
                simplifyTree(root);
            }
            else {

                BTNode** rID = findChangeableID(op, root->right);
                BTNode** lINT = findChangeableINT(op, root->left);
                if (root->left->data == INT) lINT = &(root->left);
                if ((rID != NULL && lINT != NULL)) {
                    BTNode* temp = *rID;
                    *rID = *lINT;
                    *lINT = temp;
                    simplifyTree(root);
                }
                else {
                    break;
                }
            }
        }
        
    }
    
    commuteSimplify(root->left);
    commuteSimplify(root->right);
}