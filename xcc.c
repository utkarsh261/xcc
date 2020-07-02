
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/***************************************************
*
*                  Tokenizer
*      Flattens the input into a list of Tokens.
*
****************************************************/

// token type
typedef enum {
  TK_RESERVED, // symbol
  TK_NUM,      // integer token
  TK_IDENT,    // Identifiers
  TK_EOF,      // token indicating EO input
} TokenKind;

typedef struct Token Token;

/** struct of a single node of the linked list of tokens **/

// token type
struct Token {
  TokenKind kind; // token type
  Token *next;    // next input token
  int val;        // If kind is TK_NUM, its number
  char *str;      // token string
  int len;
};

// Input program in a string for error message display
char *user_input;
// Token currently focusedン, i.e. current pointer.
Token *token;

// function for reporting errors
// takes the same arguments as printf
void error(char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  fprintf(stderr, "\n");
  exit(1);
}

// Reports error at location and exits.
void error_at(char *loc, char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);

  int pos = loc - user_input;
  fprintf(stderr, "%s\n", user_input);
  fprintf(stderr, "%*s", pos, ""); // print pos spaces.
  fprintf(stderr, "^ ");
  vfprintf(stderr, fmt, ap);
  fprintf(stderr, "\n");
  exit(1);
}
// If the next token is the expected symbol, read one token forward
// returns true. Otherwise, it returns false.
bool consume(char *op) {
  if (token->kind != TK_RESERVED || strlen(op) != token->len ||
      memcmp(token->str, op, token->len))
    return false;
  token = token->next;
  return true;
}

// Expect Identifier and move forward
Token *consume_ident() {
  if (token->kind != TK_IDENT)
    return NULL;
  Token *t = token;
  token = token->next;
  return t;
}

// If the next token is the expected symbol, read one token.
// otherwise report an error.
void expect(char *op) {
  if (token->kind != TK_RESERVED || strlen(op) != token->len ||
      memcmp(token->str, op, token->len))
    error_at(token->str, "expected '%c' ", op);
  token = token->next;
}

// If the next token is a number, read one token and return that number.
// otherwise report an error.
int expect_number() {
  if (token->kind != TK_NUM)
    error_at(token->str, "expected a number");
  int val = token->val;
  token = token->next;
  return val;
}

// Ensure that the current token is TK_IDENT.
char *expect_ident(void) {
  if (token->kind != TK_IDENT)
    error_at(token->str, "expected an identifier");
  char *s = strndup(token->str, token->len);
  token = token->next;
  return s;
}
bool at_eof() { return token->kind == TK_EOF; }

/*****
* create a new node (token) and connect to cur, 
* i.e. rest of the linked list
*****/
Token *new_token(TokenKind kind, Token *cur, char *str, int len) {
  Token *tok = calloc(1, sizeof(Token));
  tok->kind = kind;
  tok->str = str;
  cur->next = tok;
  tok->len = len;
  return tok;
}

bool startswith(char *p, char *q) { return memcmp(p, q, strlen(q)) == 0; }

static bool is_alpha(char c) {
  return ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c == '_';
}

static bool is_alnum(char c) { return is_alpha(c) || ('0' <= c && c <= '9'); }

/******
* tokenize the user input and return it, basically creation of a liked list
******/

char *starts_with_reserved(char *p) {
  // Keyword
  static char *kw[] = {"return", "if", "else", "while", "for"};

  for (int i = 0; i < sizeof(kw) / sizeof(*kw); i++) {
    int len = strlen(kw[i]);
    if (startswith(p, kw[i]) && !is_alnum(p[len]))
      return kw[i];
  }

  // Multi-letter punctuator
  static char *ops[] = {"==", "!=", "<=", ">="};

  for (int i = 0; i < sizeof(ops) / sizeof(*ops); i++)
    if (startswith(p, ops[i]))
      return ops[i];

  return NULL;
}


Token *tokenize() {
  char *p = user_input;
  Token head;
  head.next = NULL;
  Token *cur = &head;

  while (*p) {
    // skip whitespaceプ
    if (isspace(*p)) {
      p++;
      continue;
    }

    // Keywords or multi-letter punctuators
    char *keyw = starts_with_reserved(p);
    if (keyw) {
      int len = strlen(keyw);
      cur = new_token(TK_RESERVED, cur, p, len);
      p += len;
      continue;
    }

    // Identifier
    if (is_alpha(*p)) {
      char *q = p++;
      while (is_alnum(*p))
        p++;
      cur = new_token(TK_IDENT, cur, q, p - q);
      continue;
    }

    // Single-letter punctuator
    if (ispunct(*p)) {
      cur = new_token(TK_RESERVED, cur, p++,
                      1); // create a new token (node), join to the current.
      continue;
    }

    if (isdigit(*p)) {
      cur = new_token(TK_NUM, cur, p, 0);
      char *q = p;
      cur->val = strtol(p, &p, 10);
      cur->len = p - q;
      continue;
    }

    error_at(p, "invalid token");
  }

  new_token(TK_EOF, cur, p, 0);
  return head.next;
}
/**************************************************************
*
*                Parser - recursive descent parser
*
* Current Grammar:
* program    = stmt*
* stmt       = "return"  expr ";" | expr ";"
*              | "if" "(" expr ")" stmt ("else" stmt)?
*              | "while" "(" expr ")" stmt
*              | "for" "(" expr? ";" expr ";" expr ";" ")" stmt  
*              | "{" stmt* "}" 
*              | expr ";"
* expr       = assign
* assign     = equality ("=" assign)?
* equality   = relational ("==" relational | "!=" relational)*
* relational = add ("<" add | "<=" add | ">" add | ">=" add)*
* add        = mul ("+" mul | "-" mul)*
* mul        = unary ("*" unary | "/" unary)*
* unary      = ("+" | "-")? primary
* primary    = num | ident | "(" expr ")"
*
***************************************************************/

// Local variable
typedef struct Var Var;
struct Var {
  Var *next;
  char *name; // Variable name
  int offset; // Offset from RBP
};


// Node type of Abstract syntax tree
typedef enum {
  ND_ADD,
  ND_SUB,
  ND_MUL,
  ND_DIV,
  ND_NUM,
  ND_ASSIGN,    // =
  ND_EQ,        // ==
  ND_NE,        // !=
  ND_LT,        // <
  ND_LE,        // <=
  ND_VAR,       // variable
  ND_IF,        // if statement
  ND_WHILE,	// while statement
  ND_BLOCK,     // {}
  ND_FUNCALL,   // Function call        
  ND_FOR,       // for statement
  ND_EXPR_STMT, // expression statement
  ND_RET,       // return statement
} NodeKind;

typedef struct Node Node;

// single node type if the abstract syntax tree
struct Node {
  NodeKind kind; // node type
  Node *next;    // Next node (nodes are seperated by ';')

  Node *lhs;     // pointer to left
  Node *rhs;     // pointer to right

  // "if" or "while" or "for"
  Node *cond;
  Node *then;
  Node *els;
  Node *init; // initial value
  Node *inc;  // increament value
  
  // Block of code, {}
  Node *body; 

  // function name
  char* funcname;
  Node* args;

  Var *var;     // if kind == ND_VAR
  long val;      // only used when kind is ND_NUM
};

typedef struct Function Function;
struct Function {
  Function *next;
  char *name;
  Node *node;
  Var *locals;
  int stack_size;
};

// All local variable instances created during parsing are
// accumulated to this list.
Var *locals;

// Find a local variable by name.
static Var *find_var(Token *tok) {
  for (Var *var = locals; var; var = var->next)
    if (strlen(var->name) == tok->len && !strncmp(tok->str, var->name, tok->len))
      return var;
  return NULL;
}


/** create a new node (token) **/
Node *new_node(NodeKind kind, Node *lhs, Node *rhs) {
  Node *node = calloc(1, sizeof(Node));
  node->kind = kind;
  node->lhs = lhs;
  node->rhs = rhs;
  return node;
}

// if kind is Variable
Node *new_var_node(Var *var) {
  Node *node = new_node(ND_VAR, NULL, NULL);
  node->var = var;
  return node;
}

// if kind is num.
Node *new_node_num(int val) {
  Node *node = calloc(1, sizeof(Node));
  node->kind = ND_NUM;
  node->val = val;
  return node;
}
Var *new_lvar(char *name) {
  Var *var = calloc(1, sizeof(Var));
  var->next = locals;
  var->name = name;
  locals = var;  //var added to the list of locals
  return var;
}

Function *program();
Function *function();
Node *stmt();
Node *expr();
Node *assign();
Node *equality();
Node *mul();
Node *primary();
Node *unary();
Node *relational();
Node *add();

// program = function*
Function *program() {
  Function head = {};
  Function *cur = &head;

  while(!at_eof()) {
    cur->next = function();
    cur = cur->next;
  }

  return head.next;
}

// function = ident "(" ")" "{" stmt* "}"
Function *function(){ 
  locals = NULL;

  char *name = expect_ident();
  expect("(");
  expect(")");
  expect("{");

  Node head = {};
  Node *cur = &head;

  while (!consume("}")) {
    cur->next = stmt();
    cur = cur->next;
  }
  Function *fn = calloc(1, sizeof(Function));
  fn->name = name;
  fn->node = head.next;
  fn->locals = locals;
  return fn;

  // Comment for some old code;
  // now the pointer prog, has all the local variables and points to the head of the list of 
  // nodes in the program, nodes are all the statements seperated by ';'
  // so we call codegen giving it prog, codegen now iterates at all the nodes of the prog, i.e. all the
  // statements seperated by ;
}

Node *read_expr_stmt(void) {
  return new_node(ND_EXPR_STMT, expr(), NULL);
}

/*********************************************
*       ND_RET __         ___ND_EXPR_STMT
*                |       |          |
*                |       |          |
*   stmt   = "return"  expr ";" | expr ";"
**********************************************/

// stmt = "return" expr ";"
//      | "if" "(" expr ")" stmt ("else" stmt)?
//      | "while" "(" expr ")" stmt
//      | "for" "(" expr? ";" expr ";" expr ";" ")" stmt  
//      | "{" stmt* "}" 
//      | expr ";"

Node *stmt() {
  if (consume("return")) {
    Node *node = new_node(ND_RET, expr(), NULL);
    expect(";");
    return node;
  }

  if (consume("if")) {
    Node *node = new_node(ND_IF, NULL, NULL);
    expect("(");
    node->cond = expr();
    expect(")");
    node->then = stmt(); // Note that for `then` stmt() is called 
                         // while for `cond` expr() is called.
    if (consume("else"))
      node->els = stmt();
    return node;
  }

  if(consume("while")) {
    Node *node = new_node(ND_WHILE, NULL, NULL);
    expect("(");
    node->cond = expr();
    expect(")");
    node->then = stmt();
    return node;
  }
  if(consume("for")){
    Node* node = new_node(ND_FOR, NULL, NULL);
    expect("(");
  
    if(!consume(";")) {
      node->init = read_expr_stmt();
      expect(";");
    }
    if(!consume(";")){
      node->cond = expr();
      expect(";");
    }
    if(!consume(")")){
      node->inc = read_expr_stmt();
      expect(")");
    }
    node->then = stmt();
    return node;
  } 
  
  if (consume("{")) {
    Node head = {};
    Node* cur = &head;

    while(!consume("}")) {
      cur->next = stmt();
      cur = cur->next;
    }

    Node* node = new_node(ND_BLOCK, NULL, NULL);
    node->body = head.next;
    return node;
  } 

  Node *node = read_expr_stmt();
  expect(";");
  return node;
}
// expr = assign
Node *expr() { return assign(); }

// assign = equality ("=" assign)?
Node *assign() {
  Node *node = equality();
  if (consume("="))
    node = new_node(ND_ASSIGN, node, assign());
  return node;
}

// equality = relational ("==" relational | "!=" relational)*
Node *equality() {
  Node *node = relational();

  for (;;) {
    if (consume("=="))
      node = new_node(ND_EQ, node, relational());
    else if (consume("!="))
      node = new_node(ND_NE, node, relational());
    else
      return node;
  }
}
// relational = add ("<" add | "<=" add | ">" add | ">=" add)*
Node *relational() {
  Node *node = add();

  for (;;) {
    if (consume("<"))
      node = new_node(ND_LT, node, add());
    else if (consume("<="))
      node = new_node(ND_LE, node, add());
    else if (consume(">"))
      node = new_node(ND_LT, add(), node);
    else if (consume(">="))
      node = new_node(ND_LE, add(), node);
    else
      return node;
  }
}

// add = mul ("+" mul | "-" mul)*
Node *add() {
  Node *node = mul();

  for (;;) {
    if (consume("+")) {
      node = new_node(ND_ADD, node, mul());
    } else if (consume("-")) {
      node = new_node(ND_SUB, node, mul());
    } else {
      return node;
    }
  }
}

// with unary operations : mul = unary ("*" unary | "/" unary)*
Node *mul() {
  Node *node = unary();
  for (;;) {
    if (consume("*")) {
      node = new_node(ND_MUL, node, unary());
    } else if (consume("/")) {
      node = new_node(ND_DIV, node, unary());
    } else {
      return node;
    }
  }
}

// unary = ("+" | "-")? primary
Node *unary() {
  if (consume("+")) {
    return primary();
  }
  if (consume("-")) {
    return new_node(ND_SUB, new_node_num(0), primary());
  }
  return primary();
}

// func-args = "(" (assign ("," assign)*)? ")"

Node* func_args(){
  if(consume(")"))
    return NULL;

  Node *head = assign();
  Node *cur = head;
  while(consume(",")){
    cur->next = assign();
    cur = cur->next;
  }
  expect(")");
  return head;
}

// primary = "(" expr ")" | ident func-args? | num
Node *primary() {
  // if next token is "(" it should be a "(" expr ")"
  if (consume("(")) {
    Node *node = expr();
    expect(")");
    return node;
  }
  // It could be a Identifier, accept that
  Token *tok = consume_ident();
  if (tok) {
    // Function call
    if(consume("(")){
      Node* node = new_node(ND_FUNCALL, NULL, NULL);
      node->funcname = strndup(tok->str, tok->len);
      node->args = func_args();
      return node;
    }
    
    // Variable

    // If the variable had previously appeared, use offset. 
    // For a new variable, create a new lvar, set a new offset and use that offset.
    Var *var = find_var(tok);
    if (!var)
      var = new_lvar(strndup(tok->str, tok->len));
      // The strndup() function returns a pointer to a new string which is a
      // duplicate of the string s but only copies at most n bytes
    // now that it is ensured that offset is set, create a new node for the variable.
    return new_var_node(var);
  }
  //  except number 
  return new_node_num(expect_number());
}

/*************************************************************
*
*                Asm Code Generation
*
*  traversing the Abstract Syntax Tree to emit assembly.
*
**************************************************************/

int labelseq = 1;
char *argreg[] = {"rdi", "rsi", "rdx", "rcx", "r8", "r9"}; 
char *funcname;

// Pushes the given node's address to the stack.
void gen_addr(Node *node) {
  if (node->kind == ND_VAR) {
    printf("  lea rax, [rbp-%d]\n", node->var->offset);
    printf("  push rax\n");
    return;
  }

  error("not an lvalue"); // not an object that occupies memory, i.e. not a
                          // variable for example.
}

void load(void) {
  // update rax to value of the address it contains. more precisely,
  // replace the value at the top of the stack with the value it points to,
  // and set rax to the same value too   
  printf("  pop rax\n");
  printf("  mov rax, [rax]\n"); // square bracket used for dereferencing.
  printf("  push rax\n");
}

void store(void) {
  printf("  pop rdi\n"); //  value to store is in rdi.
  printf("  pop rax\n");
  printf("  mov [rax], rdi\n");
  printf("  push rdi\n");
}

void gen(Node *node) {
  switch (node->kind) {
  case ND_NUM:
    printf("  push %ld\n", node->val);
    return;
  case ND_EXPR_STMT:
    gen(node->lhs);
    printf("  add rsp, 8\n");
    return;
  case ND_VAR:
    gen_addr(node);
    load();
    return;
  case ND_ASSIGN:
    gen_addr(node->lhs);
    gen(node->rhs);
    store();
    return;
  case ND_IF: {
    int seq = labelseq++;
    if(node->els){
      gen(node->cond);
      printf("  pop rax\n");
      printf("  cmp rax, 0\n");
      printf("  je  .L.elseLABEL.%d\n", seq);
      gen(node->then);
      printf("  jmp .L.endLABEL.%d\n", seq);
      printf(".L.elseLABEL.%d:\n", seq);
      gen(node->els);
      printf(".L.endLABEL.%d:\n", seq);
    } else{
      gen(node->cond);
      printf("  pop rax\n");
      printf("  cmp rax, 0\n");
      printf("  je  .L.endLABEL.%d\n", seq);
      gen(node->then);
      printf(".L.endLABEL.%d:\n", seq);
    }
    return; 
  }
  case ND_WHILE: {
    int seq = labelseq++;
    printf(".L.beginLOOP.%d:\n", seq);
    gen(node->cond);
    printf("  pop rax\n");
    printf("  cmp rax, 0\n");
    printf("  je .L.endLOOP.%d\n", seq);
    gen(node->then);
    printf("  jmp .L.beginLOOP.%d\n", seq);
    printf(".L.endLOOP.%d:\n", seq);
    return;
  }
  case ND_FOR: {
    int seq = labelseq++;
    if(node->init)
      gen(node->init);
    printf(".L.beginLOOP.%d:\n", seq);
    if(node->cond){
      gen(node->cond);
      printf("  pop rax\n");
      printf("  cmp rax, 0\n");
      printf("  je .L.endLOOP.%d\n", seq);
    }
    gen(node->then);
    if(node->inc)
      gen(node->inc);
    printf("  jmp .L.beginLOOP.%d\n", seq);
    printf(".L.endLOOP.%d:\n", seq);
    return;
  }
  case ND_BLOCK:
    for (Node *n = node->body; n; n=n->next){
      gen(n);
    }
    return;
  case ND_FUNCALL: {
    int nargs = 0;
    for (Node* arg = node->args;arg;arg = arg=arg->next) {
      gen(arg);
      nargs++;
    }
    for (int i = nargs - 1; i >= 0; i--){
      printf("  pop %s\n", argreg[i]);
    }
  
    // We need to align RSP to a 16 byte boundary before
    // calling a function because it is an ABI requirement.
    // RAX is set to 0 for variadic function.
    int seq = labelseq++;
    printf("  mov rax, rsp\n");
    printf("  and rax, 15\n");
    printf("  jnz .L.call.%d\n", seq);
    printf("  mov rax, 0\n");
    printf("  call %s\n", node->funcname);
    printf("  jmp .L.end.%d\n", seq);
    printf(".L.call.%d:\n", seq);
    printf("  sub rsp, 8\n");
    printf("  mov rax, 0\n");
    printf("  call %s\n", node->funcname);
    printf("  add rsp, 8\n");
    printf(".L.end.%d:\n", seq);
    printf("  push rax\n");
    return;
  } 
  case ND_RET:
    gen(node->lhs);
    printf("  pop rax\n");
    printf("  jmp .L.return.%s\n", funcname);
    return;
  }
  gen(node->lhs);
  gen(node->rhs);

  printf("  pop rdi\n");
  printf("  pop rax\n");

  switch (node->kind) {
    case ND_ADD:
      printf("  add rax, rdi\n");
      break;
    case ND_SUB:
      printf("  sub rax, rdi\n");
      break;
    case ND_MUL:
      printf("  imul rax, rdi\n");
      break;
    case ND_DIV:
      printf("  cqo\n");
      printf("  idiv rdi\n");
      break;
    case ND_EQ:
      printf("  cmp rax, rdi\n");
      printf("  sete al\n");
      printf("  movzb rax, al\n");
      break;
    case ND_NE:
      printf("  cmp rax, rdi\n");
      printf("  setne al\n");
      printf("  movzb rax, al\n");
      break;
    case ND_LT:
      printf("  cmp rax, rdi\n");
      printf("  setl al\n");
      printf("  movzb rax, al\n");
      break;
    case ND_LE:
      printf("  cmp rax, rdi\n");
      printf("  setle al\n");
      printf("  movzb rax, al\n");
      break;
  }

  printf("  push rax\n");
}

/**
    Debugging functions.
**/

#define max(a, b) \
  ({ __typeof__ (a) _a = (a); \
      __typeof__ (b) _b = (b); \
    _a > _b ? _a : _b; })

const char* kindNames[] = {"ADD",
  "SUB",
  "MUL",
  "DIV",
  "NUM",
  "ASSIGN",
  "EQ",
  "NE",
  "LT",
  "LE",
  "VAR",
  "IF",
  "EXPR_STMT",
  "RET"
  };
int height(Node* root){
  if(!root)
    return 0;
  
  int h = max(height(root->lhs), height(root->rhs));
  return h+1;
}

void printGivenLevel(struct Node* root, int level) { 
    if (root == NULL) 
        return; 
    if (level == 1) 
        fprintf(stdout, "%s ", kindNames[root->kind]);
    else if (level > 1) { 
        printGivenLevel(root->lhs, level-1); 
        printGivenLevel(root->rhs, level-1); 
    } 
}  
void printLevelOrder(struct Node* root) 
{ 
    int h = height(root); 
    for (int i=1; i<=h; i++) { 
        printGivenLevel(root, i); 
        fprintf(stdout, "%s", " \n");
    } 
} 
 
void debug(Node* root){
  printLevelOrder(root);
}
/*******************************/


int main(int argc, char **argv) {
  if (argc != 2) {
    error("The number of arguments is incorrect ");
    return 1;
  }

  //  tokenize and parseuser_inputmain.c
  user_input = argv[1];
  token = tokenize(); // token pointer now points to the `head` returned by
                      // tokenizer.
  //Node *node = program();
  Function *prog = program();

  for (Function *fn = prog; fn; fn = fn->next) { 
    // Assign offsets to local variables.
    int offset = 0;
    for (Var *var = prog->locals; var; var = var->next) {
      offset += 8;
      var->offset = offset;
    }
    fn->stack_size = offset;
  }

  //for (Node *node = prog->node; node; node = node->next){
  //  debug(node);
  //}
  
  // print the first half of the assembly
  printf(".intel_syntax noprefix\n");
  
  for (Function *fn = prog; fn; fn = fn->next) {
    printf(".global %s\n", fn->name);
    printf("%s:\n", fn->name);
    funcname = fn->name;
    
    // Prologue
    printf("  push rbp\n");
    printf("  mov rbp, rsp\n");
    printf("  sub rsp, %d\n", fn->stack_size);

    // Traverse AST to generate assembly
    for (Node *node = fn->node; node; node = node->next){
      gen(node);
    }

    // Epilogue
    printf(".L.return.%s:\n", funcname);
    printf("  mov rsp, rbp\n");
    printf("  pop rbp\n");
    printf("  ret\n");
  }
  return 0;
}
