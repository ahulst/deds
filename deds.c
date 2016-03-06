#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <malloc.h>

/* Identifiers for state-based formulas */
#define B_TRUE   (0)
#define B_FALSE  (1)
#define B_PROP   (2)
#define B_NEG    (3)
#define B_AND    (4)
#define B_OR     (5)

/* Identifiers for modal formulas */
#define F_BASIC  (0)
#define F_CONJ   (1)
#define F_DISJ   (2)
#define F_ALL    (3)
#define F_EX     (4)
#define F_BOX    (5)
#define F_DIAM   (6)
#define F_CAN    (7)
#define F_DLF    (8)

/* Number of labels and transitions */
#define INIT_SIZE (10000)

/* Structure for B-formulas */
typedef struct __B
{
  int type;
  char *prop;
  struct __B *rec, *lhs, *rhs;
} B;

/* Structure for F-formulas */
typedef struct __F
{
  int type;
  char *event;
  B *basic;
  struct __F *rec, *lhs, *rhs;
} F;

/* Structure for combined state-formula pairs */
typedef struct __S
{
  char *state;
  F *form;
} S;

/* Structure for labels */
typedef struct __L
{
  char *state; 
  char *label;
} L;

/* Structure for transitions */
typedef struct __T
{
  S *begin, *end;
  char *event;
} T;

/* Structure for K-type transition systems */
typedef struct __K
{
  int num_label, num_trans;
  L **labels;
  T **trans;
  S *init;
} K;

/* Structure mainly used to create history-lists */
typedef struct __H
{
  S *sf;
  struct __H *next;
} H;

H *exp_hist = NULL, *rec_hist = NULL;

/* Construct a new part of a history-list */
H *list (S *sf, H *next)
{
  H *ret = malloc (sizeof (H)); // printf ("new list\n");
  ret->sf = sf;
  ret->next = next;
  return ret;
}

/* Construct a new state */
S *state (char *state, F *form)
{
  S *ret = malloc (sizeof (S));
  ret->state = state;
  ret->form  = form;
  return ret;
}

/* Check whether this string is a label or event */
int identifier (char *s)
{
  for ( ; *s != '\0' ; ++s)
    if (! ((*s >= '0' && *s <= '9') || (*s >= 'A' && *s <= 'Z') ||
           (*s >= 'a' && *s <= 'z') || *s == '_'))
      return 0;

  return 1;
}

/* Find operator, balance for parentheses */
int operator (char *s, char *op)
{
  int p = 0, i = 0;

  for ( ; s [i] != '\0' ; ++i)
    {
      if (s [i] == '(')
        ++p;
      else if (s [i] == ')')
        --p;
      else if (p == 0 && strncmp (s + i, op, strlen (op)) == 0)
        return i;
    }

  return -1;
}

/* Construct a new formula of type B */
B* bnew (int type, ...)
{
  va_list vl; B *ret = malloc (sizeof (B));

  va_start (vl, type);
  ret->type = type;

  if (type == B_PROP)
    ret->prop = strdup (va_arg (vl, char *));
  else if (type == B_NEG)
    ret->rec = va_arg (vl, B*);
  else if (type == B_AND || type == B_OR)
    {
      ret->lhs = va_arg (vl, B*);
      ret->rhs = va_arg (vl, B*);
    }

  if ((ret->type == B_NEG && ret->rec == NULL) || 
      ((ret->type == B_AND || ret->type == B_OR) && (ret->lhs == NULL || ret->rhs == NULL)))
    return NULL;

  va_end (vl);
  return ret;
}

/* Construct a new formula of type F */
F* fnew (int type, ...)
{
  va_list vl; F *ret = malloc (sizeof (F));

  va_start (vl, type);
  ret->type = type;

  if (type == F_BASIC)
    ret->basic = va_arg (vl, B*);
  else if (type == F_CONJ)
    {
      ret->lhs = va_arg (vl, F*);
      ret->rhs = va_arg (vl, F*);
    }
  else if (type == F_DISJ)
    {
      ret->basic = va_arg (vl, B*);
      ret->rec   = va_arg (vl, F*);
    }
  else if (type == F_ALL || type == F_EX)
    {
      ret->event = strdup (va_arg (vl, char *));
      ret->rec   = va_arg (vl, F*); 
    }
  else if (type == F_BOX)
    ret->rec = va_arg (vl, F*);
  else if (type == F_DIAM)
    ret->basic = va_arg (vl, B*);
  else if (type == F_CAN)
    ret->event = va_arg (vl, char *);

  va_end (vl);
  return ret;
}

/* Parse a B-formula */
B *bparse (char *s, int cf)
{
  int op = -1;

  if (strcmp (s, "true") == 0)
    return bnew (B_TRUE);
  else if (strcmp (s, "false") == 0)
    return bnew (B_FALSE);
  else if ((op = operator (s, "\\/")) != -1)
    return bnew (B_OR, bparse (strndup (s, op), cf), bparse (strndup (s + op + 2, strlen (s) - op - 2), cf));
  else if ((op = operator (s, "/\\")) != -1)
    return bnew (B_AND, bparse (strndup (s, op), cf), bparse (strndup (s + op + 2, strlen (s) - op - 2), cf));
  else if (s [0] == '-')
    return bnew (B_NEG, bparse (strndup (s + 1, strlen (s) - 1), cf));
  else if (s [0] == '(' && s [strlen (s) - 1] == ')')
    return bparse (strndup (s + 1, strlen (s) - 2), cf); 
  else if (identifier (s))
    return bnew (B_PROP, s);
  else if (cf || strcmp (s, "dlf") == 0)
    return NULL;

  printf ("Parse error: %s\n", s);
  exit (0);
}

/* Parse an F-formula */
F *fparse (char *s)
{
  B *bas = NULL; int op = -1; char *evt = NULL;

  if ((bas = bparse (s, 1)) != NULL)
    return fnew (F_BASIC, bas);
  else if ((op = operator (s, "/\\")) != -1)
    return fnew (F_CONJ, fparse (strndup (s, op)), fparse (strndup (s + op + 2, strlen (s) - op - 2)));
  else if ((op = operator (s, "\\/")) != -1)
    return fnew (F_DISJ, bparse (strndup (s, op), 0), fparse (strndup (s + op + 2, strlen (s) - op - 2)));
  else if (s [0] == '[' && strstr (s, "]") != NULL && (op = (int) (strstr (s, "]") - s)) != 1 &&
           op != strlen (s) - 1 && identifier (evt = strndup (s + 1, op - 1)))
    return fnew (F_ALL, evt, fparse (strdup (s + op + 1)));
  else if (s [0] == '[' && s [1] == ']')
    return fnew (F_BOX, fparse (strdup (s + 2)));
  else if (s [0] == '<' && strstr (s, ">") != NULL && (op = (int) (strstr (s, ">") - s)) != 1 &&
           op != strlen (s) - 1 && identifier (evt = strndup (s + 1, op - 1)) && evt [0] != '_')
    return fnew (F_EX, evt, fparse (strdup (s + op + 1)));
  else if (s [0] == '<' && strstr (s, ">") != NULL && (op = (int) (strstr (s, ">") - s)) != 1 &&
           op == strlen (s) - 1 && identifier (evt = strndup (s + 1, op - 1)))
    return fnew (F_CAN, evt);
  else if (s [0] == '<' && s [1] == '>')
    return fnew (F_DIAM, bparse (strdup (s + 2), 0));
  else if (strcmp (s, "dlf") == 0)
    return fnew (F_DLF);
  else if (s [0] == '(' && s [strlen (s) - 1] == ')')
    return fparse (strndup (s + 1, strlen (s) - 2));

  printf ("Parse error: %s\n", s);
  exit (0);
}

/* Convert a B-formula to a string */
char *bstring (B *b)
{
  char *rec = NULL, *lhs = NULL, *rhs = NULL, *ret = NULL;

  if (b->type == B_TRUE)
    return "true";
  else if (b->type == B_FALSE)
    return "false";
  else if (b->type == B_PROP)
    return strdup (b->prop);
  else if (b->type == B_NEG)
    {
      rec = bstring (b->rec);
      ret = malloc (strlen (rec) + 4);
      strcpy (ret, "-");
      if (b->rec->type == B_AND || b->rec->type == B_OR)
        strcat (ret, "(");
      strcat (ret, rec);
      if (b->rec->type == B_AND || b->rec->type == B_OR)
        strcat (ret, ")");
      return ret;
    }
  else if (b->type == B_AND)
    {
      lhs = bstring (b->lhs);
      rhs = bstring (b->rhs);
      ret = malloc (strlen (lhs) + strlen (rhs) + 7);
      if (b->lhs->type == B_OR)
        strcpy (ret, "(");
      else
        ret [0] = '\0';
      strcat (ret, lhs);
      if (b->lhs->type == B_OR)
        strcat (ret, ")");
      strcat (ret, "/\\");
      if (b->rhs->type == B_OR)
        strcat (ret, "(");
      strcat (ret, rhs);
      if (b->rhs->type == B_OR)
        strcat (ret, ")");
      return ret;
    }
  else if (b->type == B_OR)
    {
      lhs = bstring (b->lhs);
      rhs = bstring (b->rhs);
      ret = malloc (strlen (lhs) + strlen (rhs) + 3);
      strcpy (ret, lhs);
      strcat (ret, "\\/");
      strcat (ret, rhs);
      return ret;
    }

  printf ("Attempting to convert unknown formula type to string\n");
  exit (0);
}

/* Convert an F-formula to a string */
char *fstring (F *f)
{
  char *ret = NULL, *rec = NULL, *lhs = NULL, *rhs = NULL;

  if (f->type == F_BASIC)
    return bstring (f->basic);
  else if (f->type == F_CONJ)
    {
      lhs = fstring (f->lhs);
      rhs = fstring (f->rhs);
      ret = malloc (strlen (lhs) + strlen (rhs) + 7);

      if (f->lhs->type == F_DISJ || (f->lhs->type == F_BASIC && f->lhs->basic->type >= B_AND))
        strcpy (ret, "(");
      else
        ret [0] = '\0';
      strcat (ret, lhs);
      if (f->lhs->type == F_DISJ || (f->lhs->type == F_BASIC && f->lhs->basic->type >= B_AND))
        strcat (ret, ")");
      strcat (ret, "/\\");
      if (f->rhs->type == F_DISJ || (f->rhs->type == F_BASIC && f->rhs->basic->type >= B_AND))
        strcat (ret, "(");
      strcat (ret, rhs);
      if (f->rhs->type == F_DISJ || (f->rhs->type == F_BASIC && f->rhs->basic->type >= B_AND))
        strcat (ret, ")");
      return ret;
    }
  else if (f->type == F_DISJ)
    {
      lhs = bstring (f->basic);
      rhs = fstring (f->rec);
      ret = malloc (strlen (lhs) + strlen (rhs) + 7);

      if (f->basic->type >= B_AND)
        strcpy (ret, "(");
      else
        ret [0] = '\0';
      strcat (ret, lhs);
      if (f->basic->type >= B_AND)
        strcat (ret, ")");
      strcat (ret, "\\/");
      if (f->rec->type == F_CONJ || f->rec->type == F_DISJ || 
         (f->rec->type == F_BASIC && f->rec->basic->type >= B_AND))
        strcat (ret, "(");
      strcat (ret, rhs);
      if (f->rec->type == F_CONJ || f->rec->type == F_DISJ || 
         (f->rec->type == F_BASIC && f->rec->basic->type >= B_AND))
        strcat (ret, ")");
      return ret;
    }
  else if (f->type == F_ALL)
    {
      rec = fstring (f->rec);
      ret = malloc (strlen (f->event) + strlen (rec) + 5);

      strcpy (ret, "[");
      strcat (ret, f->event);
      strcat (ret, "]");
      if (f->rec->type == F_CONJ || f->rec->type == F_DISJ ||
         (f->rec->type == F_BASIC && f->rec->basic->type >= B_AND))
        strcat (ret, "(");
      strcat (ret, rec);
      if (f->rec->type == F_CONJ || f->rec->type == F_DISJ ||
         (f->rec->type == F_BASIC && f->rec->basic->type >= B_AND))
        strcat (ret, ")");
      return ret;
    }
  else if (f->type == F_EX)
    {
      rec = fstring (f->rec);
      ret = malloc (strlen (f->event) + strlen (rec) + 5);

      strcpy (ret, "<");
      strcat (ret, f->event);
      strcat (ret, ">");
      if (f->rec->type == F_CONJ || f->rec->type == F_DISJ ||
         (f->rec->type == F_BASIC && f->rec->basic->type >= B_AND))
        strcat (ret, "(");
      strcat (ret, rec);
      if (f->rec->type == F_CONJ || f->rec->type == F_DISJ ||
         (f->rec->type == F_BASIC && f->rec->basic->type >= B_AND))
        strcat (ret, ")");
      return ret;
    }
  else if (f->type == F_BOX)
    {
      rec = fstring (f->rec);
      ret = malloc (strlen (rec) + 4);

      strcpy (ret, "[]");
      if (f->rec->type == F_CONJ || f->rec->type == F_DISJ || 
         (f->rec->type == F_BASIC && f->rec->basic->type >= B_AND))
        strcat (ret, "(");
      strcat (ret, rec);
      if (f->rec->type == F_CONJ || f->rec->type == F_DISJ ||
         (f->rec->type == F_BASIC && f->rec->basic->type >= B_AND))
        strcat (ret, ")");
      return ret;
    }
  else if (f->type == F_DIAM)
    {
      rec = bstring (f->basic);
      ret = malloc (strlen (rec) + 4);

      strcpy (ret, "<>");
      if (f->basic->type >= B_AND)
        strcat (ret, "(");
      strcat (ret, rec);
      if (f->basic->type >= B_AND)
        strcat (ret, ")");
      return ret;
    }
  else if (f->type == F_CAN)
    {
      ret = malloc (strlen (f->event) + 3);
      strcpy (ret, "<");
      strcat (ret, f->event);
      strcat (ret, ">");
      return ret;
    }
  else if (f->type == F_DLF)
    return "dlf";

  printf ("Attempting to convert unknown formula type to string\n");
  exit (0);
}

/* Read the initial basic system from file */
K *initial (char *fname, F *form)
{
  char *line = NULL, *com1 = NULL, *com2 = NULL; 
  size_t size = 0, i = 0; 
  FILE *fp = fopen (fname, "r"); 
  K *k = malloc (sizeof (K));

  k->labels = malloc (INIT_SIZE * sizeof (L *));
  k->num_label = 0;
  k->trans = malloc (INIT_SIZE * sizeof (T *));
  k->num_trans = 0;

  for (i = 0 ; i < INIT_SIZE ; ++i)
    { k->labels [i] = NULL ; k->trans [i] = NULL; }

  while (getline (&line, &size, fp) != -1 && !feof (fp))
    {
      if (line [strlen (line) - 1] == '\n')
        line [strlen (line) - 1] = '\0';

      if (line [0] == 'I' && line [1] == ':')
        {
          k->init = malloc (sizeof (S));
          k->init->state = strdup (line + 2);
          k->init->form = form;
        }

      if (line [0] == 'L' && line [1] == ':' && (com1 = strstr (line, ",")) != NULL)
        {
          k->labels [k->num_label] = malloc (sizeof (L));
          k->labels [k->num_label]->state = strndup (line + 2, com1 - line - 2);
          k->labels [k->num_label]->label = strdup (com1 + 1);
          k->num_label += 1;
        }

      if (line [0] == 'T' && line [1] == ':' && (com1 = strstr (line, ",")) != NULL && 
         (com2 = strstr (com1 + 1, ",")) != NULL)
        {
          k->trans [k->num_trans] = malloc (sizeof (T));
          k->trans [k->num_trans]->begin = malloc (sizeof (S));
          k->trans [k->num_trans]->end   = malloc (sizeof (S));
          k->trans [k->num_trans]->begin->state = strndup (line + 2, com1 - line - 2);
          k->trans [k->num_trans]->begin->form  = fnew (F_BASIC, bnew (B_TRUE));
          k->trans [k->num_trans]->event = strndup (com1 + 1, com2 - com1 - 1);
          k->trans [k->num_trans]->end->state = strdup (com2 + 1);
          k->trans [k->num_trans]->end->form  = fnew (F_BASIC, bnew (B_TRUE));
          k->num_trans += 1;
        }
    }

  return k;
}

/* Print an overview of a K-structure */
void overview (K *k)
{
  int i = 0;

  printf ("Initial state: (%s, %s)\n", k->init->state, fstring (k->init->form));
  for (i = 0 ; i < k->num_label ; ++i)
    if (k->labels [i] != NULL)
      printf ("Label: %s |-> %s\n", k->labels [i]->state, k->labels [i]->label);
  for (i = 0 ; i < k->num_trans ; ++i)
    if (k->trans [i] != NULL)
      printf ("Transition: (%s, %s) -(%s)-> (%s, %s)\n", k->trans [i]->begin->state, 
        fstring (k->trans [i]->begin->form), k->trans [i]->event, k->trans [i]->end->state,
        fstring (k->trans [i]->end->form));
}

/* Test equality for two B-formulas */
int bequal (B *b, B *c)
{
  if (b->type != c->type)
    return 0;
  else if (b->type == B_PROP)
    return strcmp (b->prop, c->prop) == 0;
  else if (b->type == B_NEG)
    return bequal (b->rec, c->rec);
  else if (b->type == B_AND || b->type == B_OR)
    return bequal (b->lhs, c->lhs) && bequal (b->rhs, c->rhs);
  else
    return 1;
}

/* Test equality for two F-formulas */
int fequal (F *f, F *g)
{
  if (f->type != g->type)
    return 0;
  else if (f->type == F_BASIC)
    return bequal (f->basic, g->basic);
  else if (f->type == F_CONJ)
    return fequal (f->lhs, g->lhs) && fequal (f->rhs, g->rhs);
  else if (f->type == F_DISJ)
    return bequal (f->basic, g->basic) && fequal (f->rec, g->rec);
  else if (f->type == F_ALL)
    return strcmp (f->event, g->event) == 0 && fequal (f->rec, g->rec);
  else if (f->type == F_EX)
    return strcmp (f->event, g->event) == 0 && fequal (f->rec, g->rec);
  else if (f->type == F_BOX)
    return fequal (f->rec, g->rec);
  else if (f->type == F_DIAM)
    return bequal (f->basic, g->basic);
  else if (f->type == F_CAN)
    return strcmp (f->event, g->event) == 0;
  else
    return 0;
}

/* Validity of state-based formulas */
int bval (L **labels, int num_labels, char *state, B *b)
{
  int i = 0;
 
  if (b->type == B_TRUE)
    return 1;
  else if (b->type == B_FALSE)
    return 0;
  else if (b->type == B_PROP)
    {
      for ( ; i < num_labels ; ++i)
        if (strcmp (labels [i]->state, state) == 0 && strcmp (labels [i]->label, b->prop) == 0)
          return 1;

      return 0;
    }
  else if (b->type == B_NEG)
    return !bval (labels, num_labels, state, b->rec);
  else if (b->type == B_AND)
    return bval (labels, num_labels, state, b->lhs) && bval (labels, num_labels, state, b->rhs);
  else if (b->type == B_OR)
    return bval (labels, num_labels, state, b->lhs) || bval (labels, num_labels, state, b->rhs);
  else
    return 0;
}

/* Find an item in a list */
int in (S *sf, H* l)
{
  return (l == NULL) ? 0 : 
    ((strcmp (sf->state, l->sf->state) == 0 && fequal (sf->form, l->sf->form)) ? 1 : in (sf, l->next));
}

int sub (L **labels, int num_labels, char *state, F *f, F* g)
{
  if (fequal (f, g))
    return 1;
  else if (g->type == F_CONJ)
    return sub (labels, num_labels, state, f, g->lhs) || sub (labels, num_labels, state, f, g->rhs);
  else if (g->type == F_DISJ && !bval (labels, num_labels, state, g->basic))
    return sub (labels, num_labels, state, f, g->rec);
  else if (g->type == F_BOX)
    return sub (labels, num_labels, state, f, g->rec);
  else
    return 0;
}

/* Construct the list of formula-reductions */
H *red (L** labels, int num_labels, S *sf, char *event, char *end)
{
  H *lhs = NULL, *rhs = NULL, *lit = NULL, *rit = NULL, *ret = NULL, *rec = NULL;

  if (sf->form->type == F_BASIC)
    return list (state (end, fnew (F_BASIC, bnew (B_TRUE))), NULL);
  else if (sf->form->type == F_CONJ)
    {
      lhs = red (labels, num_labels, state (sf->state, sf->form->lhs), event, end);
      rhs = red (labels, num_labels, state (sf->state, sf->form->rhs), event, end);

      for (lit = lhs ; lit != NULL ; lit = lit->next)
        for (rit = rhs ; rit != NULL ; rit = rit->next)
          if (sub (labels, num_labels, end, rit->sf->form, lit->sf->form))
            ret = list (lit->sf, ret);
          else
            ret = list (state (end, fnew (F_CONJ, lit->sf->form, rit->sf->form)), ret);

      return ret;
    }
  else if (sf->form->type == F_DISJ)
    {
      if (bval (labels, num_labels, sf->state, sf->form->basic))
        return list (state (end, fnew (F_BASIC, bnew (B_TRUE))), NULL);
      else
        return red (labels, num_labels, state (sf->state, sf->form->rec), event, end);
    }
  else if (sf->form->type == F_ALL)
    {
      if (strcmp (sf->form->event, event) == 0)
        return list (state (end, sf->form->rec), NULL);
      else
        return list (state (end, fnew (F_BASIC, bnew (B_TRUE))), NULL);
    }
  else if (sf->form->type == F_EX)
    {
      if (strcmp (sf->form->event, event) == 0)
        return list (state (end, sf->form->rec), list (state (end, fnew (F_BASIC, bnew (B_TRUE))), NULL));
      else
        return list (state (end, fnew (F_BASIC, bnew (B_TRUE))), NULL);
    }
  else if (sf->form->type == F_BOX)
    {
      rec = red (labels, num_labels, state (sf->state, sf->form->rec), event, end);

      for ( ; rec != NULL ; rec = rec->next)
        if (sub (labels, num_labels, end, rec->sf->form, sf->form))
          ret = list (state (end, sf->form), ret);
        else
          ret = list (state (end, fnew (F_CONJ, sf->form, rec->sf->form)), ret);

      return ret;
    }
  else if (sf->form->type == F_DIAM)
    return list (state (end, fnew (F_BASIC, bnew (B_TRUE))), NULL);
  else if (sf->form->type == F_CAN)
    return list (state (end, fnew (F_BASIC, bnew (B_TRUE))), NULL);
  else if (sf->form->type == F_DLF)
    return list (state (end, fnew (F_BASIC, bnew (B_TRUE))), NULL);
  else
    return NULL;
}

/* Add a new transition */
void add (K *Skf0, S* begin, char *event, S *end)
{
  int i = 0; T *tr = malloc (sizeof (T));

  for ( ; i < Skf0->num_trans ; ++i)
    if (strcmp (Skf0->trans [i]->begin->state, begin->state) == 0 && 
        fequal (Skf0->trans [i]->begin->form, begin->form) &&
        strcmp (Skf0->trans [i]->event, event) == 0 &&
        strcmp (Skf0->trans [i]->end->state, end->state) == 0 &&
        fequal (Skf0->trans [i]->end->form, end->form))
      return;
 
  tr->begin = begin;
  tr->event = event;
  tr->end   = end;

  Skf0->trans [Skf0->num_trans] = tr;
  Skf0->num_trans += 1;
}


/* Expand the transition system into the initial phase */
void expand (K *k, S* sf, K* Skf0)
{
  int i = 0; H *fl = NULL;

  if (in (sf, exp_hist))
    return;

  exp_hist = list (sf, exp_hist);

  for ( ; i < k->num_trans ; ++i)
    {
      if (strcmp (sf->state, k->trans [i]->begin->state) == 0)
        {
          for (fl = red (k->labels, k->num_label, sf, k->trans [i]->event, k->trans [i]->end->state) ; 
               fl != NULL ; fl = fl->next)
            {
              add (Skf0, sf, k->trans [i]->event, fl->sf);
              expand (k, fl->sf, Skf0);
            }
        }
    }
}

/* Check whether a formula <>b is valid */
int diamond (K* k, S *s, B *b, H *l)
{
  int i = 0;

  if (bval (k->labels, k->num_label, s->state, b))
    return 1;
  if (in (s, l))
    return 0;

  for (i = 0 ; i < k->num_trans ; ++i)
    {
      if (strcmp (k->trans [i]->begin->state, s->state) == 0 && fequal (k->trans [i]->begin->form, s->form) &&
          diamond (k, k->trans [i]->end, b, list (s, l)))
        return 1;
    }

  return 0;
}

/* Implementation of the synthesizability predicate */
int synthesizable (K* k, S* s, F *f)
{
  int i = 0;

  if (f->type == F_BASIC)
    return bval (k->labels, k->num_label, s->state, f->basic);
  else if (f->type == F_CONJ)
    return synthesizable (k, s, f->lhs) && synthesizable (k, s, f->rhs);
  else if (f->type == F_DISJ)
    return bval (k->labels, k->num_label, s->state, f->basic) || synthesizable (k, s, f->rec);
  else if (f->type == F_ALL)
    return 1;
  else if (f->type == F_EX)
    {
      for (i = 0 ; i < k->num_trans ; ++i)
        if (strcmp (k->trans [i]->begin->state, s->state) == 0 && fequal (k->trans [i]->begin->form, s->form) &&
            strcmp (k->trans [i]->event, f->event) == 0 && 
            sub (k->labels, k->num_label, s->state, f->rec, k->trans [i]->end->form) &&
            synthesizable (k, k->trans [i]->end, f->rec))
          return 1;

      return 0;
    }
  else if (f->type == F_BOX)
    return synthesizable (k, s, f->rec);
  else if (f->type == F_DIAM)
    return diamond (k, s, f->basic, NULL);
  else if (f->type == F_CAN)
    {
      for (i = 0 ; i < k->num_trans ; ++i)
        if (strcmp (k->trans [i]->begin->state, s->state) == 0 && fequal (k->trans [i]->begin->form, s->form) &&
            strcmp (k->trans [i]->event, f->event) == 0)
          return 1;

      return 0;
    }
  else if (f->type == F_DLF)
    {
      for (i = 0 ; i < k->num_trans ; ++i)
        if (strcmp (k->trans [i]->begin->state, s->state) == 0 && fequal (k->trans [i]->begin->form, s->form))
          return 1;

      return 0;
    }

  return 0;
}

/* Check whether to keep a transition */
int keep (K *k, S *s, H *l)
{
  int i = 0;

  if (in (s, l))
    return 1;
  if (!synthesizable (k, s, s->form))
    return 0;

  for (i = 0 ; i < k->num_trans ; ++i)
    if (strcmp (k->trans [i]->begin->state, s->state) == 0 && fequal (k->trans [i]->begin->form, s->form) &&
        k->trans [i]->event [0] == '_' && !keep (k, k->trans [i]->end, list (s, l)))
      return 0;

  return 1;
}

/* Recursively test transitions for removal */
void recursive (K* k, K *knew, S *s)
{
  int i = 0;

  if (in (s, rec_hist))
    return;

  rec_hist = list (s, rec_hist);

  for (i = 0 ; i < k->num_trans ; ++i)
    if (strcmp (k->trans [i]->begin->state, s->state) == 0 && fequal (k->trans [i]->begin->form, s->form) &&
        keep (k, k->trans [i]->end, NULL))
      {
        add (knew, k->trans [i]->begin, k->trans [i]->event, k->trans [i]->end);
        recursive (k, knew, k->trans [i]->end);
      }
}

/* Single removal step in the control synthesis procedure */
K *removal (K *k)
{
  K* knew = malloc (sizeof (K));

  knew->num_label = k->num_label;
  knew->num_trans = 0;
  knew->labels    = k->labels;
  knew->init      = k->init;
  knew->trans     = malloc (INIT_SIZE * sizeof (T*));

  rec_hist = NULL; 
  recursive (k, knew, knew->init);

  return knew;
}

/* Implementation of the completeness predicate */
int complete (K *k)
{
  int i = 0;

  if (!synthesizable (k, k->init, k->init->form))
    return 0;

  for (i = 0 ; i < k->num_trans ; ++i)
    if (!synthesizable (k, k->trans [i]->end, k->trans [i]->end->form))
      return 0;

  return 1;
}

/* Perform the actual synthesis itself */
K *prune (K* k)
{
  K* knew = removal (k);

  printf ("Synthesis iteration\n");

  if (k->num_trans == knew->num_trans)
    return complete (knew) ? knew : NULL;
  else
    return prune (knew);
}

int main (int argc, char *argv [])
{
  K *k = NULL, *Skf0 = malloc (sizeof (K)), *Skfn = NULL;

  if (argc != 3)
    printf ("Usage: %s <file> <formula>\n", argv [0]);
  else
    {
      k = initial (argv [1], fparse (argv [2]));
      Skf0->init      = k->init;
      Skf0->labels    = k->labels;
      Skf0->num_label = k->num_label;
      Skf0->trans     = malloc (INIT_SIZE * sizeof (T *));
      Skf0->num_trans = 0;
      expand (k, k->init, Skf0);

      printf ("Synthesis starting point:\n");
      overview (Skf0);

      Skfn = prune (Skf0);

      if (Skfn == NULL)
        printf ("Synthesis was not successful!\n");
      else
        {
          printf ("Synthesis result:\n");
          overview (Skfn);
        }
    }

  return 0;
}

