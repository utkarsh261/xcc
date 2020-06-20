#include <ctype.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//
// Tokenizer
//

// token type
typedef enum {
  TK_RESERVED, // symbol
  TK_NUM,      // integer token
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
  if (token->kind != TK_RESERVED || strlen(op)!=token->len || memcmp(token->str, op, token->len))
    return false;
  token = token->next;
  return true;
}

// If the next token is the expected symbol, read one token.
// otherwise report an error.
void expect(char *op) {
  if (token->kind != TK_RESERVED || strlen(op) != token->len ||
      memcmp(token->str, op, token->len))
    error_at(token->str, "expected '%c', op");
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

/** create a new node (token) and connect to cur, i.e. rest of the linked
 * list**/
Token *new_token(TokenKind kind, Token *cur, char *str, int len) {
  Token *tok = calloc(1, sizeof(Token));
  tok->kind = kind;
  tok->str = str;
  cur->next = tok;
  tok->len = len; 
  return tok;
}

bool startswith(char *p, char *q) {
  return memcmp(p, q, strlen(q)) == 0;
}


/** tokenize the user input and return it, basically creation of a liked list
 **/
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
    //Multi letter Punctuator
    if (startswith(p, "==") || startswith(p, "!=") ||
        startswith(p, "<=") || startswith(p, ">=")) {
      cur = new_token(TK_RESERVED, cur, p, 2); // create a new token (node), join to the current.
      p += 2;
      continue;
    }

    // Single-letter punctuator
    if (strchr("+-*/()<>", *p)) {
      cur = new_token(TK_RESERVED, cur, p++, 1);  // create a new token (node), join to the current.
      continue;
    }

    if (isdigit(*p)) {
      cur = new_token(TK_NUM, cur, p, 0);
      char *q =  p;
      cur->val = strtol(p, &p, 10);
      cur->len = p-q;
      continue;
    }

    error_at(p, "invalid token");
  }

  new_token(TK_EOF, cur, p, 0);
  return head.next;
}

//
//  Parser
//

// Node type of Abstract syntax tree
typedef enum {
  ND_ADD,
  ND_SUB,
  ND_MUL,
  ND_DIV,
  ND_NUM,
  ND_EQ,  // ==
  ND_NE,  // !=
  ND_LT,  // <
  ND_LE,  // <=
} NodeKind;

typedef struct Node Node;

// single node type if the abstract syntax tree
struct Node {
  NodeKind kind; // node type
  Node *lhs;     // pointer to left
  Node *rhs;     // pointer to right
  int val;       // only used when kind is ND_NUM
};

/** create a new node (token) **/
Node *new_node(NodeKind kind, Node *lhs, Node *rhs) {
  Node *node = calloc(1, sizeof(Node));
  node->kind = kind;
  node->lhs = lhs;
  node->rhs = rhs;
  return node;
}

// if kind is node.
Node *new_node_num(int val) {
  Node *node = calloc(1, sizeof(Node));
  node->kind = ND_NUM;
  node->val = val;
  return node;
}

Node *expr();
Node *mul();
Node *primary();
Node *unary();
Node *equality();
Node *relational();
Node *add();

// expr = mul ("+" mul | "-" mul)*
// after adding comparision operators 
// new grammar : 
// expr = equality
Node *expr(){
  return equality();
}

// equality = relational ("==" relational | "!=" relational)*
Node *equality(){
  Node *node = relational();

  for(;;){
    if (consume("=="))
      node = new_node(ND_EQ, node, relational());
    else if(consume("!="))
      node = new_node(ND_NE, node, relational());
    else
      return node;
  }
}
// relational = add ("<" add | "<=" add | ">" add | ">=" add)*
Node *relational(){
  Node *node = add();

  for(;;){
    if(consume("<"))
      node = new_node(ND_LT, node, add());
    else if(consume("<="))
      node = new_node(ND_LE, node, add());
    else if(consume(">"))
      node = new_node(ND_LT, add(), node);
    else if(consume(">="))
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

// mul = primary ("*" primary | "/" primary)*
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
Node *unary(){
  if(consume("+")){
    return primary();
  }
  if(consume("-")){
    return new_node(ND_SUB, new_node_num(0), primary());
  }
  return primary();
}
// primary = "(" expr ")" | num
Node *primary() {
  // if next token is "(" it should be a "(" expr ")"
  if (consume("(")) {
    Node *node = expr();
    expect(")");
    return node;
  }

  // otherwise it should be a number
  return new_node_num(expect_number());
}

//
// asm code generation
//

void gen(Node *node) {
  if (node->kind == ND_NUM) {
    printf("  push %d\n", node->val);
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
  Node *node = expr();
  // print the first half of the assembly
  printf(".intel_syntax noprefix\n");
  printf(".globl main\n");
  printf("main:\n");

  // Traverse AST to generate assembly
  gen(node);

  printf("  pop rax\n");
  printf("  ret\n");
  return 0;
}