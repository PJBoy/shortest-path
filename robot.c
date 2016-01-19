#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct building
{
    unsigned int left, top, right, bottom;
} building;

// Holds the arrays of information about all the vertices
typedef struct vertex
{
    unsigned int* pre; // The predecessor character, 'N', 'E', 'S', 'W' or 'T' (never eat Shredded Wheat or toast)
    unsigned int* neighbours; // 
    unsigned int* qid; // The priority with the queue while processing in Dijkstra's (sometimes known as the auxiliary array) to speed up decreaseKey
    unsigned int* d; // The distance from the origin
    // unsigned int boxType; // 
    // qid doesn't exist until boxType has finished, so this define just saves memory allocation
    #define boxType qid
    #define BOX_HORIZONTAL 1
    #define BOX_VERTICAL 2
    #define BOX_CORNER 3
} vertex;

// This can be considered to be a linked list path... but edge is a better name
typedef struct edge
{
    unsigned int v; // The destination vertex
    unsigned int next; // The next edge (if any)
    unsigned int w; // The weight of the edge
    char direction; // 'N', 'E', 'S', 'W' or 'T'
    // The number of edges to initially allocate for
    #define INITIAL_EDGES 512
} edge;


typedef struct queue
{
    unsigned int* vertices; // The list of vertices in the queue
    unsigned int n_vertices; // The number of vertices in the queue
} queue;

vertex vertices;
edge* edges;
unsigned int n, nSquared; // The length and area of the map respectively
queue q;

unsigned int minimum() // And delete
{
    unsigned int v;
    unsigned int currEntry;

    // Ran out of vertices
    if (!q.n_vertices)
        return -1;

    // Extract the minimum (will be returned after queue is fixed)
    v = q.vertices[1];

    // Replace the entry (with the queue tail)
    q.vertices[1] = q.vertices[q.n_vertices];
    --q.n_vertices;
    vertices.qid[q.vertices[1]] = 1;
    
    // Fix queue
    currEntry = 1;
    for (;;)
    {
        unsigned int smallest;
        unsigned int left = currEntry<<1;
        unsigned int right = left+1;

        // Find smallest entry of the current of its children
        if (left <= q.n_vertices && vertices.d[q.vertices[left]] < vertices.d[q.vertices[currEntry]])
            smallest = left;
        else
            smallest = currEntry;
        if (right <= q.n_vertices && vertices.d[q.vertices[right]] < vertices.d[q.vertices[smallest]])
            smallest = right;

        // Hopefully the queue is consistent
        if (smallest == currEntry)
            break;

        // If not, swap current entry with the smallest, rinse and repeat
        else
        {
            unsigned int t = q.vertices[currEntry];
            q.vertices[currEntry] = q.vertices[smallest];
            q.vertices[smallest] = t;

            vertices.qid[q.vertices[currEntry]] = currEntry;
            vertices.qid[q.vertices[smallest]] = smallest;

            currEntry = smallest;
        }
    }
    
    return v;
}

void decreaseKey(unsigned int index, unsigned int key)
{
    // The easy part
    vertices.d[q.vertices[index]] = key;

    // The more difficult part.
    // Ascend up the tree, swapping the current node with its parent until queue is consistent
    while (index > 1 && vertices.d[q.vertices[index>>1]] > key)
    {
        unsigned int t;

        unsigned int t_vertex = q.vertices[index];
        q.vertices[index] = q.vertices[index>>1];
        q.vertices[index>>1] = t_vertex;

        t = vertices.qid[q.vertices[index]];
        vertices.qid[q.vertices[index]] = vertices.qid[q.vertices[index>>1]];
        vertices.qid[q.vertices[index>>1]] = t;

        index >>= 1;
    }
}

void boxHorizontal(unsigned int x, unsigned int y, int d_x)
{
    // Boundary check
    if ((int)y < 0 || y >= n)
        return;

    else
    {
        unsigned int i, xMin;
        unsigned int v;

        // We don't take kindly to vertices whose current path contain a horizontal edge
        if (vertices.neighbours[y*n + x])
        {
            edge* e;
            for (e = &edges[vertices.neighbours[y*n + x]];; e = &edges[e->next])
            {
                if (e->direction == 'E' || e->direction == 'W')
                    return;
                if (!e->next)
                    break;
            }
        }

        // This minimum of n-1 and the end point
        xMin = x+d_x;
        if (xMin > n-1)
            xMin = n-1;

        // Apply BOX_HORIZONTAL to all vertices along the given line
        v = y*n+x;
        for (i = xMin-x+1; i; --i, ++v)
            vertices.boxType[v] |= BOX_HORIZONTAL;

        // Extend this line until either the city boundary or a building
        v = y*n + xMin;
        for (i = n-xMin; i && vertices.d[v]+1; --i, ++v)
            vertices.boxType[v] |= BOX_HORIZONTAL;

        // Extend this line to the left, analogous to the above
        v = y*n + x-1;
        for (i = x; i && vertices.d[v]+1; --i, --v)
            vertices.boxType[v] |= BOX_HORIZONTAL;
    }
}

void boxVertical(unsigned int x, unsigned int y, int d_y)
{
    // Boundary check
    if ((int)x < 0 || x >= n)
        return;

    else
    {
        unsigned int i, yMin;
        unsigned int v;

        // We don't take kindly to vertices whose current path contain a vertical edge
        if (vertices.neighbours[y*n + x])
        {
            edge* e;
            for (e = &edges[vertices.neighbours[y*n + x]];; e = &edges[e->next])
            {
                if (e->direction == 'N' || e->direction == 'S')
                    return;
                if (!e->next)
                    break;
            }
        }

        // This minimum of n-1 and the end point
        yMin = y+d_y;
        if (yMin > n-1)
            yMin = n-1;

        // Apply BOX_VERTICAL to all vertices along the given line
        v = y*n+x;
        for (i = yMin-y+1; i; --i, v += n)
            vertices.boxType[v] |= BOX_VERTICAL;

        // Extend this line until either the city boundary or a building
        v = yMin*n + x;
        for (i = n-yMin; i && vertices.d[v]+1; --i, v += n)
            vertices.boxType[v] |= BOX_VERTICAL;

        // Extend this line up, analogous to the above
        v = (y-1)*n + x;
        for (i = y; i && vertices.d[v]+1; --i, v -= n)
            vertices.boxType[v] |= BOX_VERTICAL;
    }
}

void addEdge(unsigned int s, unsigned int d, unsigned int w, char direction)
{
    static unsigned int n_e = 1; // The number of edges (so far)
    static unsigned int edgesMax = INITIAL_EDGES; // The number of edges allocated for

    // Handle currently allocated memory being full
    if (n_e == edgesMax)
    {
        edgesMax <<= 1;
        edges = (edge*)realloc(edges, edgesMax*sizeof(edge));
    }
    edges[n_e].v = d; // Assign destination vertex
    edges[n_e].w = w; // Assign weight
    edges[n_e].direction = direction; // Assign direction
    edges[n_e].next = vertices.neighbours[s]; // Edge's next edge becomes source vertex's neighbour edge...
    vertices.neighbours[s] = n_e; // ...while source's neighbour edge becomes current edge
    ++n_e;
}

int main(int argc, char* argv[])
{
    building* buildings;
    unsigned int i, j, y, *d_y, size, n_b = 0, buildingMax = 512;
    unsigned int min_vertex, currVertex;
    char* path;

    // Initialisation //
    FILE* file = fopen(argv[1], "rb");

    fscanf(file, "%d\n", &n);
    nSquared = n*n;
    
    vertices.d = (unsigned int*)calloc(nSquared, sizeof(unsigned int));
    vertices.neighbours = (unsigned int*)calloc(nSquared, sizeof(unsigned int));
    vertices.pre = (unsigned int*)malloc(nSquared * sizeof(unsigned int));
    vertices.qid = (unsigned int*)calloc(nSquared, sizeof(unsigned int));
    edges = (edge*)malloc(INITIAL_EDGES * sizeof(edge));
    buildings = (building*)malloc(buildingMax * sizeof(building));

    // Read in city
    for (;;)
    {
        char obstacle = fgetc(file);

        // Read all buildings, set vertex distances to pseudo-infinite
        if (obstacle == 'b')
        {
            unsigned int left, top, right, bottom, y, d_x;
            fscanf(file, " %d %d %d %d\n", &left, &top, &right, &bottom);
            --left; --top;

            // Fill vertex distances with -1 for building areas (-1 = 0xFFFF...)
            d_x = (right-left) * sizeof(unsigned int);
            for (y = top*n + left; y < bottom*n; y += n)
                memset(&vertices.d[y], 0xFF, d_x);
            
            // Memory management
            if (n_b == buildingMax)
            {
                buildingMax <<= 1;
                buildings = (building*)realloc(buildings, buildingMax);
            }

            // Add entry to list of buildings
            buildings[n_b].left = left;
            buildings[n_b].top = top;
            buildings[n_b].right = right-1;
            buildings[n_b].bottom = bottom-1;
            ++n_b;
            continue;
        }

        // Read all portals
        if (obstacle == 't')
        {
            unsigned int s_x, s_y, d_x, d_y, w;
            fscanf(file, " %d %d %d %d %d\n", &s_x, &s_y, &d_x, &d_y, &w);
            --s_x; --s_y; --d_x; --d_y;

            addEdge(s_y*n+s_x, d_y*n+d_x, w, 'T');

            // Not technically a box but...
            boxHorizontal(s_x, s_y, 0);
            boxVertical(s_x, s_y, 0);
            boxHorizontal(d_x, d_y, 0);
            boxVertical(d_x, d_y, 0);
            continue;
        }
        break;
    }
    fclose(file);

    // Draw box around map
    boxHorizontal(0, 0, n-1); // Top edge
    boxVertical(0, 0, n-1); // Left edge
    boxHorizontal(0, n-1, n-1); // Bottom edge
    boxVertical(n-1, 0, n-1); // Right edge

    // Draw box around each building
    for (i = 0; i < n_b; ++i)
    {
        building b = buildings[i];
        boxHorizontal(b.left, b.top-1, b.right-b.left); // Just above top edge
        boxVertical(b.left-1, b.top, b.bottom-b.top); // Just left of left edge
        boxHorizontal(b.left, b.bottom+1, b.right-b.left); // Just below bottom edge
        boxVertical(b.right+1, b.top, b.bottom-b.top); // Just right of right edge
    }
    free(buildings);

    // Calculate distances from buildings
    d_y = (unsigned int*)calloc(n, sizeof(unsigned int));
    for (y = 0; y < n; ++y)
    {
        unsigned int x, d_x = 0;
        for (x = 0; x < n; ++x)
        {
            unsigned int v = y*n + x;

            // Within building, so distance from building is reset
            if (!(vertices.d[v]+1))
            {
                d_x = d_y[x] = 0;
                continue;
            }

            // For each intersection of building edges:
            if (vertices.boxType[v] == BOX_CORNER)
            {
                // If not adjacently below building edge:
                if (d_y[x] > 0)
                {
                    addEdge(v - d_y[x]*n, v,            d_y[x], 'S');
                    addEdge(v,            v - d_y[x]*n, d_y[x], 'N');
                }

                // If not adjacently to the right of building edge:
                if (d_x > 0)
                {
                    addEdge(v - d_x, v,       d_x, 'E');
                    addEdge(v,       v - d_x, d_x, 'W');
                }
                vertices.qid[v] = 0;

                // Intersection found, so distance from building will be (at least) 1 from both directions
                d_x = d_y[x] = 1;
                vertices.d[v] = -1;

                continue;
            }
            // No buildings here, increment distance from building
            ++d_x;
            ++d_y[x];
        }
    }
    free(d_y);

    // Start vertex is obviously zero
    vertices.d[0] = 0;

    // Initialise queue
    q.vertices = (unsigned int*)malloc((nSquared+1) * sizeof(unsigned int));

    // Queue size
    size = nSquared;

    // Populate queue with those vertices with neighbours
    for (i = 0, j = 1; i < nSquared; ++i)
    {
        if (!vertices.neighbours[i])
        {
            --size;
            continue;
        }
        q.vertices[j] = i;
        vertices.qid[i] = j;
        ++j;
    }

    // Update queue size w.r.t. number of vertices with neighbours
    q.n_vertices = size;

    // Dijkstra's :+)
    for (;;)
    {
        edge* e;

        // Find and delete the current minimum weight vertex
        min_vertex = minimum();

        // Termination condition, either no more vertices or no more valid vertices
        if (!(min_vertex+1) || !(vertices.d[min_vertex]+1))
            break;
        
        // Update each neighbours weight w.r.t. current vertex's weight. A.K.A. 'relax'
        // Also add predecessor for route tracking
        if (vertices.neighbours[min_vertex])
        {
            for (e = &edges[vertices.neighbours[min_vertex]]; ; e = &edges[e->next])
            {
                unsigned int v = e->v;
                unsigned int d = vertices.d[min_vertex] + e->w;
                if (vertices.d[v] > d)
                {
                    vertices.pre[v] = min_vertex;
                    decreaseKey(vertices.qid[v], d);
                }
                if (!e->next)
                    break;
            }
        }
    }

    // Goodbye queue
    free(q.vertices);
    free(vertices.qid);


    // Print path //
    currVertex = nSquared-1;
    
    // No path exists to final vertex, so return empty-handed (what a waste of precious CPU time)
    if (!(vertices.d[currVertex]+1))
        return 0;

    // Allocate worst-case path length
    path = (char*)malloc(vertices.d[currVertex] + 2);

    // Last two characters: new-line and null-terminator
    path[vertices.d[currVertex]] = '\n'; path[vertices.d[currVertex]+1] = 0;

    // Working backwards from the end of the string:
    for (i = vertices.d[currVertex]-1; currVertex; currVertex = vertices.pre[currVertex])
    {
        edge* e;
        // Find the neighbour responsible for current vertex
        for (e = &edges[vertices.neighbours[vertices.pre[currVertex]]]; e->v != currVertex && e->next; e = &edges[e->next]);

        // If portal, print the one character and move on
        if (e->direction == 'T')
        {
            path[i] = 'T';
            --i;
            continue;
        }

        // If compass direction, print the direction however many times is necessary
        for (j = i+1 - e->w; j <= i; ++j)
            path[j] = e->direction;
        i -= e->w;
    }
    printf(&path[i+1]);
    free(path);

    free(edges);
    free(vertices.d);
    free(vertices.neighbours);
    free(vertices.pre);

    // Phew...
    return 0;
}