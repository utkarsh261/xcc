#include <ctype.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/***************************************************
*
*                  Tokenizer
*         Flattens the input into a list of Tokens.
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

    if (startswith(p, "return") && !is_alnum(p[6])) {
      cur = new_token(TK_RESERVED, cur, p, 6);
      p += 6;
      continue;
    }

    // Identifier
    if ('a' <= *p && *p <= 'z') {
      cur = new_token(TK_IDENT, cur, p++, 1);
      continue;
    }

    // Multi letter Punctuator
    if (startswith(p, "==") || startswith(p, "!=") || startswith(p, "<=") ||
        startswith(p, ">=")) {
      cur = new_token(TK_RESERVED, cur, p,
                      2); // create a new token (node), join to the current.
      p += 2;
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
* stmt   = "return"  expr ";" | expr ";"
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
  char name;     // if kind == ND_VAR
  long val;      // only used when kind is ND_NUM
};

/** create a new node (token) **/
Node *new_node(NodeKind kind, Node *lhs, Node *rhs) {
  Node *node = calloc(1, sizeof(Node));
  node->kind = kind;
  node->lhs = lhs;
  node->rhs = rhs;
  return node;
}

// if kind is Variable
Node *new_var_node(char name) {
  Node *node = new_node(ND_VAR, NULL, NULL);
  node->name = name;
  return node;
}

// if kind is num.
Node *new_node_num(int val) {
  Node *node = calloc(1, sizeof(Node));
  node->kind = ND_NUM;
  node->val = val;
  return node;
}

Node *program();
Node *stmt();
Node *expr();
Node *assign();
Node *equality();
Node *mul();
Node *primary();
Node *unary();
Node *relational();
Node *add();

// program = stmt*
Node *program(void) {
  Node head = {};
  Node *cur = &head;

  while (!at_eof()) {
    cur->next = stmt();
    cur = cur->next;
  }
  return head.next;
}
/*********************************************
*       ND_RET __         ___ND_EXPR_STMT
*                |       |          |
*                |       |          |
*   stmt   = "return"  expr ";" | expr ";"
**********************************************/

// stmt = "return" expr ";"
//      | expr ";"
Node *stmt() {
  if (consume("return")) {
    Node *node = new_node(ND_RET, expr(), NULL);
    expect(";");
    return node;
  }

  Node *node = new_node(ND_EXPR_STMT, expr(), NULL);
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

// primary = "(" expr ")" | ident | num
Node *primary() {
  // if next token is "(" it should be a "(" expr ")"
  if (consume("(")) {
    Node *node = expr();
    expect(")");
    return node;
  }
  // It could be a Identifier
  Token *tok = consume_ident();
  if (tok)
    return new_var_node(*tok->str);
  // otherwise it should be a number
  return new_node_num(expect_number());
}

/*************************************************************
*
*                Asm Code Generation
*
*  traversing the Abstract Syntax Tree to emit assembly.
*
**************************************************************/

// Pushes the given node's address to the stack.
void gen_addr(Node *node) {
  if (node->kind == ND_VAR) {
    int offset = (node->name - 'a' + 1) * 8;
    printf("  lea rax, [rbp-%d]\n", offset);
    printf("  push rax\n");
    return;
  }

  error("not an lvalue"); // not an object that occupies memory, i.e. not a
                          // variable for example.
}

void load(void) {
  printf("  pop rax\n");
  printf("  mov rax, [rax]\n");
  printf("  push rax\n");
}

void store(void) {
  printf("  pop rdi\n");
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
  case ND_RET:
    gen(node->lhs);
    printf("  pop rax\n");
    printf("  jmp .L.return\n");
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

int main(int argc, char **argv) {
  if (argc != 2) {
    error("The number of arguments is incorrect ");
    return 1;
  }

  //  tokenize and parseuser_inputmain.c
  user_input = argv[1];
  token = tokenize(); // token pointer now points to the `head` returned by
                      // tokenizer.
  Node *node = program();
  // print the first half of the assembly
  printf(".intel_syntax noprefix\n");
  printf(".globl main\n");
  printf("main:\n");

  // Prologue, reserve area for 26 variables.
  printf("  push rbp\n");
  printf("  mov rbp, rsp\n");
  printf("  sub rsp, 208\n");
  // There are 26 letters in the alphabet,
  // so we push down RSP by 26 x 8 or 208 bytes when calling a function,
  // we will be able to secure the area for all 1-character variables.

  // Traverse AST to generate assembly
  for (Node *n = node; n; n = n->next) {
    gen(n);
  }
  // Epilogue
  printf(".L.return:\n");
  printf("  mov rsp, rbp\n");
  printf("  pop rbp\n");

  printf("  ret\n");
  return 0;
}