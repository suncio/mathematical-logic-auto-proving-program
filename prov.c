#include <stdio.h>
#include <ctype.h>

#define IMPLY 0
#define UNKNOWN 2
#define LEAF 4
#define NEGATIVE 8
#define VIRTUAL 16
#define MP_ROOT 32

#define MAX_NODE_NUM 256

struct Node {
    int type, left, right, next;
};

int pos[MAX_NODE_NUM];
int pt[MAX_NODE_NUM];
Node buf[MAX_NODE_NUM];
int pos_c = 0;
void out();

/*
 * 判断arr[index]是否为arr[root]的后代或本身
 */
bool is_child(Node *arr, int root, int index) 
{
    if (root == index) 
        return true;
    int type = arr[root].type;
    if (type & (UNKNOWN | LEAF)) 
        return false;
    if (type & (NEGATIVE | VIRTUAL)) 
        return is_child(arr, arr[root].left, index);
    else 
        return is_child(arr, arr[root].left, index) || is_child(arr, arr[root].right, index);
}

/*
 * 判断arr[a]和arr[b]是否有可能在语法结构上完全相同
 * 并修改它们的结构以保证相等性约束
 * (匹配unknown未知结点时将其修改为virtual结点指向被匹配的结点)
 * 比较时virtual虚结点会被收缩，自动越过
 */
bool equal(Node *arr, int a, int b) {
    if (a == b) 
        return true;
    if (arr[a].type == VIRTUAL) 
        return equal(arr, arr[a].left, b);
    if (arr[b].type == VIRTUAL) 
        return equal(arr, a, arr[b].left);
    if (arr[a].type == UNKNOWN) 
    {
        // 避免一个virtual虚结点指向其祖先形成环
        if (is_child(arr, b, a)) 
            return false;
        arr[a].type = VIRTUAL;
        arr[a].left = b;
        return true;
    }
    if (arr[b].type == UNKNOWN) {
        // 避免一个virtual虚结点指向其祖先形成环
        if (is_child(arr, a, b)) 
            return false;
        arr[b].type = VIRTUAL;
        arr[b].left = a;
        return true;
    }
    /*
     * arr[a]和arr[b]类型不同时返回false
     * 这里注意MP_ROOT(32)是一种特殊的IMPLY(0)结点
     */
    if ((arr[a].type ^ arr[b].type) & (LEAF | NEGATIVE)) 
        return false;
    if (arr[a].type == LEAF) 
    {
        if (arr[a].left == arr[b].left) 
            return true;
        else 
            return false;
    }
    if(arr[a].type == NEGATIVE) 
        return equal(arr, arr[a].left, arr[b].left);
    return equal(arr, arr[a].left, arr[b].left) && equal(arr, arr[a].right, arr[b].right);
}

void block_copy(Node *old, Node *arr) 
{
    for (int i = 0; i < MAX_NODE_NUM; i++) 
    {
        arr[i].left = old[i].left;
        arr[i].right = old[i].right;
        arr[i].next = old[i].next;
        arr[i].type = old[i].type;
    }
}

/*
 * 将arr[index](应为unknown未知结点)拓展为IMPLY结点
 * 并包含两个unknown未知子结点
 * count为arr中最后一个结点的索引值
 */
void extend_unknown_node(Node *arr, int index, int count) 
{
    arr[index].type = IMPLY;
    arr[index].left = count + 1;
    arr[index].right = count + 2;
    arr[count + 1].type = UNKNOWN;
    arr[count + 2].type = UNKNOWN;
}

/*
 * 将arr[index](应为unknown未知结点)拓展为negative结点
 * 并包含一个unknown未知子结点
 * count为arr中最后一个结点的索引值
 */
void extend_neg_node(Node *arr, int index, int count) 
{
    arr[index].type = NEGATIVE;
    arr[index].left = count + 1;
    arr[count + 1].type = UNKNOWN;
}

/*
 * IDA*算法核心函数
 * @param root  为当前迭代待证命题根结点索引
 * @param count 为old中最后一个结点的索引值
 * @param proof 为剩余未证命题数
 * @param bound 为剩余迭代次数
 */
bool ida(Node *old, int root, int count, int proof, int bound) 
{
    if (count >= MAX_NODE_NUM) 
    {
        printf("!!!!!!!!!!!\n");
        return false;
    }
    Node arr[MAX_NODE_NUM];
    if (bound < proof) 
        return false;
    if (proof == 0) 
    {
        block_copy(old, buf);
        return true;
    }
    if (bound == 0) 
        return false;
    int ro = root;
    int type = old[ro].type;
    while (type == VIRTUAL) 
    {
        ro = old[ro].left;
        type = old[ro].type;
    }
    if (type == LEAF) 
        return false;
    if (type == NEGATIVE) 
        goto MP_PROOF;
    if (type == MP_ROOT) 
        goto L2_PROOF;

    L3_PROOF:
    {
        int lll, lrl, rl, rr;
        block_copy(old, arr);
        int c = count;
        if (type == UNKNOWN) 
        {
            extend_unknown_node(arr, ro, c);
            extend_unknown_node(arr, c + 1, c + 2);
            extend_neg_node(arr, c + 3, c + 4);
            extend_neg_node(arr, c + 4, c + 5);
            extend_unknown_node(arr, c + 2, c + 6);
            lll = c + 5;
            lrl = c + 6;
            rl = c + 7;
            rr = c + 8;
            c += 8;
        } 
        else 
        {
            int r = arr[ro].right;
            int rt = arr[r].type;
            while (rt == VIRTUAL) 
            {
                r = arr[r].left;
                rt = arr[r].type;
            }
            if (rt & (NEGATIVE | LEAF)) 
                goto MP_PROOF;
            if (rt == UNKNOWN) 
            {
                extend_unknown_node(arr, r, c);
                rl = c + 1;
                rr = c + 2;
                c += 2;
            } 
            else 
            {
                rl = arr[r].left;
                rr = arr[r].right;
            }
            int l = arr[ro].left;
            int lt = arr[l].type;
            while (lt == VIRTUAL) 
            {
                l = arr[l].left;
                lt = arr[l].type;
            }
            if (lt & (NEGATIVE | LEAF)) 
                goto L1_PROOF;
            if (lt == UNKNOWN) 
            {
                extend_unknown_node(arr, l, c);
                extend_neg_node(arr, c + 1, c + 2);
                extend_neg_node(arr, c + 2, c + 3);
                lll = c + 3;
                lrl = c + 4;
                c += 4;
            } 
            else 
            {
                int lr = arr[l].right;
                int lrt = arr[lr].type;
                while (lrt == VIRTUAL) 
                {
                    lr = arr[lr].left;
                    lrt = arr[lr].type;
                }
                if (lrt == UNKNOWN) 
                {
                    extend_neg_node(arr, lr, c);
                    lrl = c + 1;
                    c += 1;
                } 
                else if (lrt == NEGATIVE) 
                    lrl = arr[lr].left;
                else if (lrt == LEAF) 
                    goto L1_PROOF;
                else 
                    goto L2_PROOF;
                int ll = arr[l].left;
                int llt = arr[ll].type;
                while (llt == VIRTUAL) 
                {
                    ll = arr[ll].left;
                    llt = arr[ll].type;
                }
                if (llt == UNKNOWN) 
                {
                    extend_neg_node(arr, ll, c);
                    lll = c + 1;
                    c += 1;
                } 
                else if (llt == NEGATIVE) 
                    lll = arr[ll].left;
                else 
                    goto L2_PROOF;
            }
        }
        if (equal(arr, lll, rr) && equal(arr, lrl, rl)) 
        {
            if (ida(arr, arr[root].next, c, proof - 1, bound - 1)) 
            {
                pos[pos_c] = ro;
                pt[pos_c] = 3;
                pos_c++;
                return true;
            }
        }
    }

    L2_PROOF:
    {
        int ll, lrl, lrr, rll, rlr, rrl, rrr;
        block_copy(old, arr);
        int c = count;
        if (type == UNKNOWN) 
        {
            extend_unknown_node(arr, ro, c);
            extend_unknown_node(arr, c + 1, c + 2);
            extend_unknown_node(arr, c + 4, c + 4);
            extend_unknown_node(arr, c + 2, c + 6);
            extend_unknown_node(arr, c + 7, c + 8);
            extend_unknown_node(arr, c + 8, c + 10);
            ll = c + 3;
            lrl = c + 5;
            lrr = c + 6;
            rll = c + 9;
            rlr = c + 10;
            rrl = c + 11;
            rrr = c + 12;
            c += 12;
        } 
        else 
        {
            int l = arr[ro].left;
            int lt = arr[l].type;
            while (lt == VIRTUAL) 
            {
                l = arr[l].left;
                lt = arr[l].type;
            }
            if (lt & (NEGATIVE | LEAF)) goto L1_PROOF;
            if (lt == UNKNOWN) 
            {
                extend_unknown_node(arr, l, c);
                extend_unknown_node(arr, c + 2, c + 2);
                ll = c + 1;
                lrl = c + 3;
                lrr = c + 4;
                c += 4;
            } 
            else 
            {
                ll = arr[l].left;
                int lr = arr[l].right;
                int lrt = arr[lr].type;
                while (lrt == VIRTUAL) 
                {
                    lr = arr[lr].left;
                    lrt = arr[lr].type;
                }
                if (lrt & (NEGATIVE | LEAF)) goto L1_PROOF;
                if (lrt == UNKNOWN) 
                {
                    extend_unknown_node(arr, lr, c);
                    lrl = c + 1;
                    lrr = c + 2;
                    c += 2;
                } 
                else 
                {
                    lrl = arr[lr].left;
                    lrr = arr[lr].right;
                }
            }
            int r = arr[ro].right;
            int rt = arr[r].type;
            while (rt == VIRTUAL) 
            {
                r = arr[r].left;
                rt = arr[r].type;
            }
            if (rt & (NEGATIVE | LEAF)) 
                goto MP_PROOF;
            if (rt == UNKNOWN) 
            {
                extend_unknown_node(arr, r, c);
                extend_unknown_node(arr, c + 1, c + 2);
                extend_unknown_node(arr, c + 2, c + 4);
                rll = c + 3;
                rlr = c + 4;
                rrl = c + 5;
                rrr = c + 6;
                c += 6;
            } 
            else 
            {
                int rl = arr[r].left;
                int rlt = arr[rl].type;
                while (rlt == VIRTUAL) 
                {
                    rl = arr[rl].left;
                    rlt = arr[rl].type;
                }
                if (rlt & (NEGATIVE | LEAF)) 
                    goto L1_PROOF;
                if (rlt == UNKNOWN) 
                {
                    extend_unknown_node(arr, rl, c);
                    rll = c + 1;
                    rlr = c + 2;
                    c += 2;
                } 
                else 
                {
                    rll = arr[rl].left;
                    rlr = arr[rl].right;
                }
                int rr = arr[r].right;
                int rrt = arr[rr].type;
                while (rrt == VIRTUAL) 
                {
                    rr = arr[rr].left;
                    rrt = arr[rr].type;
                }
                if (rrt & (NEGATIVE | LEAF)) goto L1_PROOF;
                if (rrt == UNKNOWN) 
                {
                    extend_unknown_node(arr, rr, c);
                    rrl = c + 1;
                    rrr = c + 2;
                    c += 2;
                } 
                else 
                {
                    rrl = arr[rr].left;
                    rrr = arr[rr].right;
                }
            }
        }
        if (equal(arr, rll, rrl) && equal(arr, ll, rll) && equal(arr, lrl, rlr) && equal(arr, lrr, rrr)) 
        {
            if (ida(arr, arr[root].next, c, proof - 1, bound - 1)) 
            {
                pos[pos_c] = ro;
                pt[pos_c] = 2;
                pos_c++;
                return true;
            }
        }
    }

    L1_PROOF:
    {
        int l, rr;
        block_copy(old, arr);
        int c = count;
        if (type == UNKNOWN) 
        {
            extend_unknown_node(arr, ro, c);
            extend_unknown_node(arr, c + 2, c + 2);
            l = c + 1;
            rr = c + 4;
            c += 4;
        } 
        else 
        {
            l = arr[ro].left;
            int r = arr[ro].right;
            int rt = arr[r].type;
            while (rt == VIRTUAL) 
            {
                r = arr[r].left;
                rt = arr[r].type;
            }
            if (rt & (NEGATIVE | LEAF | MP_ROOT)) goto MP_PROOF;
            if (rt == UNKNOWN) 
            {
                extend_unknown_node(arr, r, c);
                rr = c + 2;
                c += 2;
            } 
            else rr = arr[r].right;
        }
        if (equal(arr, l, rr)) 
        {
            if (ida(arr, arr[root].next, c, proof - 1, bound - 1)) 
            {
                pos[pos_c] = ro;
                pt[pos_c] = 1;
                pos_c++;
                return true;
            }
        }
    }

    MP_PROOF:
    {
        old[count + 1].type = UNKNOWN;
        old[count + 1].next = old[root].next;
        old[count + 2].type = MP_ROOT;
        old[count + 2].left = count + 1;
        old[count + 2].right = ro;
        old[count + 2].next = count + 1;
        if (ida(old, count + 2, count + 2, proof + 1, bound - 1)) 
        {
            pos[pos_c] = ro;
            pt[pos_c] = 0;
            pos_c++;
            return true;
        }
    }
    return false;
}

void print_tree(int i) 
{
    switch (buf[i].type) 
    {
        case UNKNOWN:
            pos_c++;
            buf[i].type = LEAF;
            buf[i].left = - pos_c;
            printf("[%d]", - pos_c);
            break;
        case LEAF:
            printf("[%d]", buf[i].left);
            break;
        case NEGATIVE:
            printf("~");
            print_tree(buf[i].left);
            break;
        case VIRTUAL:
            print_tree(buf[i].left);
            break;
        default:
            printf("(");
            print_tree(buf[i].left);
            printf("->");
            print_tree(buf[i].right);
            printf(")");
    }
}

void out() 
{
    int t = pos_c;
    pos_c = 0;
    for (int i = 0; i < t; i++) 
    {
        printf("L%d:", pt[i]);
        print_tree(pos[i]);
        printf("\n");
    }
}

FILE *fp;
int all = 0;
int word;
int in(Node *t) 
{
    int c = all;
    switch (word) 
    {
        case '/':
            all++;
            word = fgetc(fp);
            t[c].left = in(t);
            t[c].type = NEGATIVE;
            return c;
        case '(':
            all++;
            word = fgetc(fp);
            t[c].left = in(t);
            word = fgetc(fp);
            t[c].right = in(t);
            fgetc(fp);
            t[c].type = 0;
            return c;
        case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9':
        {
            all++;
            int n = word - '0';
            for (word = fgetc(fp); isdigit(word); word = fgetc(fp)) 
            {
                n = n * 10 + word - '0';
            }
            t[c].left = n;
            t[c].type = LEAF;
            return c;
        }
        default:
            fgetc(fp);
            return in(t);
    }
}

int main() {
    Node arr[MAX_NODE_NUM];
    fp=fopen("p.txt","r");
    word = fgetc(fp);
    in(arr);
    fclose(fp);
    int bound = 1;
    while (!ida(arr, 0, all - 1, 1, bound)) {
        bound += 2;
        printf("bound=%d\n", bound);
    }
    out();
    getchar();
    return 0;
}

