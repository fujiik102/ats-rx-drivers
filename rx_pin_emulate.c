
#include <inttypes.h>
#include <assert.h>

typedef int ioport_t;
typedef unsigned int bits8_uint_t;

#define IOPORT_MAX  20

bits8_uint_t g_pmrs[IOPORT_MAX];
bits8_uint_t g_pdrs[IOPORT_MAX];
bits8_uint_t g_podrs[IOPORT_MAX];
bits8_uint_t g_pidrs[IOPORT_MAX];

void writePMR_impl (ioport_t p,bits8_uint_t v)
{
    assert (0 <= p && p < IOPORT_MAX);
    g_pmrs[p] = v;
}

bits8_uint_t readPMR_impl (ioport_t p)
{
    return g_pmrs[p];
}

void writePDR_impl (ioport_t p,bits8_uint_t v)
{
    assert (0 <= p && p < IOPORT_MAX);
    g_pdrs[p] = v;
}

bits8_uint_t readPDR_impl (ioport_t p)
{
    return g_pdrs[p];
}

void writePODR_impl (ioport_t p,bits8_uint_t v)
{
    assert (0 <= p && p < IOPORT_MAX);
    g_podrs[p] = v;
}

bits8_uint_t readPODR_impl (ioport_t p)
{
    return g_podrs[p];
}

bits8_uint_t readPIDR_impl (ioport_t p)
{
    return g_pidrs[p];
}
