import GaugeFieldConstruction.Abacus
/-!
# W2 square decomposition check G
-/
set_option autoImplicit false
set_option maxRecDepth 15000
set_option maxHeartbeats 4000000
namespace YM.GaugeFieldConstruction.Vouchers.Abacus.RateG
open Cauchy Wick Raster Invoice Credit Window

def z0 : GIndex := ((false,⟨(0,(0, 0, 0)),by decide⟩):GIndex)
def z1 : GIndex := ((false,⟨(0,(0, 0, 1)),by decide⟩):GIndex)
def z2 : GIndex := ((false,⟨(0,(0, 0, 2)),by decide⟩):GIndex)
def z3 : GIndex := ((false,⟨(0,(0, 1, 0)),by decide⟩):GIndex)
def z4 : GIndex := ((false,⟨(0,(0, 1, 1)),by decide⟩):GIndex)
def z5 : GIndex := ((false,⟨(0,(0, 2, 0)),by decide⟩):GIndex)
def z6 : GIndex := ((false,⟨(0,(1, 0, 0)),by decide⟩):GIndex)
def z7 : GIndex := ((false,⟨(0,(1, 0, 1)),by decide⟩):GIndex)
def z8 : GIndex := ((false,⟨(0,(1, 1, 0)),by decide⟩):GIndex)
def z9 : GIndex := ((false,⟨(0,(2, 0, 0)),by decide⟩):GIndex)
def z10 : GIndex := ((false,⟨(1,(0, 0, 0)),by decide⟩):GIndex)
def z11 : GIndex := ((false,⟨(1,(0, 0, 1)),by decide⟩):GIndex)
def z12 : GIndex := ((false,⟨(1,(0, 0, 2)),by decide⟩):GIndex)
def z13 : GIndex := ((false,⟨(1,(0, 1, 0)),by decide⟩):GIndex)
def z14 : GIndex := ((false,⟨(1,(0, 1, 1)),by decide⟩):GIndex)
def z15 : GIndex := ((false,⟨(1,(0, 2, 0)),by decide⟩):GIndex)
def z16 : GIndex := ((false,⟨(1,(1, 0, 0)),by decide⟩):GIndex)
def z17 : GIndex := ((false,⟨(1,(1, 0, 1)),by decide⟩):GIndex)
def z18 : GIndex := ((false,⟨(1,(1, 1, 0)),by decide⟩):GIndex)
def z19 : GIndex := ((false,⟨(1,(2, 0, 0)),by decide⟩):GIndex)
def z20 : GIndex := ((false,⟨(2,(0, 0, 0)),by decide⟩):GIndex)
def z21 : GIndex := ((false,⟨(2,(0, 1, 0)),by decide⟩):GIndex)
def z22 : GIndex := ((false,⟨(2,(0, 2, 0)),by decide⟩):GIndex)
def z23 : GIndex := ((false,⟨(2,(1, 0, 0)),by decide⟩):GIndex)
def z24 : GIndex := ((false,⟨(2,(1, 1, 0)),by decide⟩):GIndex)
def z25 : GIndex := ((false,⟨(2,(2, 0, 0)),by decide⟩):GIndex)
def z26 : GIndex := ((true,⟨(0,(0, 0, 0)),by decide⟩):GIndex)
def z27 : GIndex := ((true,⟨(0,(0, 0, 1)),by decide⟩):GIndex)
def z28 : GIndex := ((true,⟨(0,(0, 0, 2)),by decide⟩):GIndex)
def z29 : GIndex := ((true,⟨(0,(0, 1, 0)),by decide⟩):GIndex)
def z30 : GIndex := ((true,⟨(0,(0, 1, 1)),by decide⟩):GIndex)
def z31 : GIndex := ((true,⟨(0,(0, 2, 0)),by decide⟩):GIndex)
def z32 : GIndex := ((true,⟨(0,(1, 0, 0)),by decide⟩):GIndex)
def z33 : GIndex := ((true,⟨(0,(1, 0, 1)),by decide⟩):GIndex)
def z34 : GIndex := ((true,⟨(0,(1, 1, 0)),by decide⟩):GIndex)
def z35 : GIndex := ((true,⟨(0,(2, 0, 0)),by decide⟩):GIndex)
def z36 : GIndex := ((true,⟨(1,(0, 0, 0)),by decide⟩):GIndex)
def z37 : GIndex := ((true,⟨(1,(0, 0, 1)),by decide⟩):GIndex)
def z38 : GIndex := ((true,⟨(1,(0, 0, 2)),by decide⟩):GIndex)
def z39 : GIndex := ((true,⟨(1,(0, 1, 0)),by decide⟩):GIndex)
def z40 : GIndex := ((true,⟨(1,(0, 1, 1)),by decide⟩):GIndex)
def z41 : GIndex := ((true,⟨(1,(0, 2, 0)),by decide⟩):GIndex)
def z42 : GIndex := ((true,⟨(1,(1, 0, 0)),by decide⟩):GIndex)
def z43 : GIndex := ((true,⟨(1,(1, 0, 1)),by decide⟩):GIndex)
def z44 : GIndex := ((true,⟨(1,(1, 1, 0)),by decide⟩):GIndex)
def z45 : GIndex := ((true,⟨(1,(2, 0, 0)),by decide⟩):GIndex)
def z46 : GIndex := ((true,⟨(2,(0, 0, 0)),by decide⟩):GIndex)
def z47 : GIndex := ((true,⟨(2,(0, 1, 0)),by decide⟩):GIndex)
def z48 : GIndex := ((true,⟨(2,(0, 2, 0)),by decide⟩):GIndex)
def z49 : GIndex := ((true,⟨(2,(1, 0, 0)),by decide⟩):GIndex)
def z50 : GIndex := ((true,⟨(2,(1, 1, 0)),by decide⟩):GIndex)
def z51 : GIndex := ((true,⟨(2,(2, 0, 0)),by decide⟩):GIndex)
def S : List GIndex := [z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15,z16,z17,z18,z19,z20,z21,z22,z23,z24,z25,z26,z27,z28,z29,z30,z31,z32,z33,z34,z35,z36,z37,z38,z39,z40,z41,z42,z43,z44,z45,z46,z47,z48,z49,z50,z51]
def T : List (Coin GIndex) := [(32834021220,[(z0,⟨1,0⟩),(z2,⟨-8,0⟩),(z5,⟨-8,0⟩),(z9,⟨-4,0⟩),(z18,⟨2,0⟩),(z37,⟨2,0⟩),(z47,⟨-2,0⟩)])
 ,(16417010610,[(z1,⟨4,0⟩),(z23,⟨-1,0⟩),(z36,⟨-1,0⟩),(z38,⟨18,0⟩),(z41,⟨6,0⟩),(z45,⟨6,0⟩)])
 ,(3456212760,[(z2,⟨38,0⟩),(z5,⟨2,0⟩),(z9,⟨4,0⟩),(z18,⟨1,0⟩),(z37,⟨-5,0⟩),(z47,⟨-1,0⟩)])
 ,(16417010610,[(z3,⟨4,0⟩),(z16,⟨-1,0⟩),(z40,⟨6,0⟩),(z46,⟨1,0⟩),(z48,⟨-18,0⟩),(z51,⟨-6,0⟩)])
 ,(65668042440,[(z4,⟨6,0⟩),(z17,⟨-1,0⟩),(z24,⟨-1,0⟩),(z39,⟨-1,0⟩)])
 ,(5529940416,[(z5,⟨30,0⟩),(z9,⟨3,0⟩),(z18,⟨-4,0⟩),(z37,⟨1,0⟩),(z47,⟨4,0⟩)])
 ,(32834021220,[(z6,⟨2,0⟩),(z13,⟨-1,0⟩),(z43,⟨6,0⟩),(z50,⟨-6,0⟩)])
 ,(2736168435,[(z7,⟨24,0⟩),(z14,⟨-6,0⟩),(z20,⟨1,0⟩),(z22,⟨-6,0⟩),(z25,⟨-18,0⟩),(z42,⟨-6,0⟩)])
 ,(2736168435,[(z8,⟨24,0⟩),(z10,⟨1,0⟩),(z12,⟨-6,0⟩),(z15,⟨-18,0⟩),(z19,⟨-18,0⟩),(z49,⟨6,0⟩)])
 ,(3581893224,[(z9,⟨22,0⟩),(z18,⟨-11,0⟩),(z37,⟨-1,0⟩),(z47,⟨1,0⟩)])
 ,(248742585,[(z10,⟨11,0⟩),(z12,⟨-90,0⟩),(z15,⟨-30,0⟩),(z19,⟨-78,0⟩),(z27,⟨-24,0⟩),(z49,⟨18,0⟩)])
 ,(16417010610,[(z11,⟨4,0⟩),(z21,⟨-1,0⟩),(z26,⟨1,0⟩),(z28,⟨-18,0⟩),(z31,⟨-6,0⟩),(z35,⟨-6,0⟩)])
 ,(257690160,[(z12,⟨139,0⟩),(z15,⟨17,0⟩),(z19,⟨9,0⟩),(z27,⟨18,0⟩),(z49,⟨3,0⟩)])
 ,(98502063660,[(z13,⟨1,0⟩),(z30,⟨-4,0⟩),(z43,⟨2,0⟩),(z50,⟨2,0⟩)])
 ,(182411229,[(z14,⟨90,0⟩),(z20,⟨5,0⟩),(z22,⟨-78,0⟩),(z25,⟨-42,0⟩),(z29,⟨24,0⟩),(z42,⟨-6,0⟩)])
 ,(436091040,[(z15,⟨52,0⟩),(z19,⟨3,0⟩),(z27,⟨6,0⟩),(z49,⟨1,0⟩)])
 ,(9850206366,[(z16,⟨5,0⟩),(z33,⟨-8,0⟩),(z40,⟨2,0⟩),(z46,⟨-1,0⟩),(z48,⟨2,0⟩),(z51,⟨22,0⟩)])
 ,(1876229784,[(z17,⟨35,0⟩),(z24,⟨-7,0⟩),(z32,⟨6,0⟩),(z39,⟨-1,0⟩)])
 ,(18762297840,[(z18,⟨7,0⟩),(z37,⟨-1,0⟩),(z47,⟨-1,0⟩)])
 ,(787229280,[(z19,⟨77,0⟩),(z27,⟨-2,0⟩),(z49,⟨-9,0⟩)])
 ,(521174940,[(z20,⟨7,0⟩),(z22,⟨-48,0⟩),(z25,⟨-48,0⟩),(z29,⟨12,0⟩),(z42,⟨-12,0⟩)])
 ,(9850206366,[(z21,⟨5,0⟩),(z26,⟨-1,0⟩),(z28,⟨2,0⟩),(z31,⟨22,0⟩),(z35,⟨6,0⟩),(z44,⟨-8,0⟩)])
 ,(1731904416,[(z22,⟨52,0⟩),(z25,⟨3,0⟩),(z29,⟨-6,0⟩),(z42,⟨-1,0⟩)])
 ,(9850206366,[(z23,⟨5,0⟩),(z34,⟨8,0⟩),(z36,⟨1,0⟩),(z38,⟨-2,0⟩),(z41,⟨-6,0⟩),(z45,⟨-22,0⟩)])
 ,(45029514816,[(z24,⟨7,0⟩),(z32,⟨-1,0⟩),(z39,⟨1,0⟩)])
 ,(787229280,[(z25,⟨77,0⟩),(z29,⟨2,0⟩),(z42,⟨9,0⟩)])
 ,(6566804244,[(z26,⟨1,0⟩),(z28,⟨8,0⟩),(z31,⟨8,0⟩),(z35,⟨4,0⟩),(z44,⟨-2,0⟩)])
 ,(42641586,[(z27,⟨20,0⟩),(z49,⟨13,0⟩)])
 ,(13133608488,[(z28,⟨10,0⟩),(z31,⟨-2,0⟩),(z35,⟨-4,0⟩),(z44,⟨-1,0⟩)])
 ,(42641586,[(z29,⟨20,0⟩),(z42,⟨13,0⟩)])
 ,(197004127320,[(z30,⟨2,0⟩),(z43,⟨1,0⟩),(z50,⟨1,0⟩)])
 ,(315206603712,[(z31,⟨2,0⟩),(z35,⟨-1,0⟩),(z44,⟨1,0⟩)])
 ,(4690574460,[(z32,⟨2,0⟩),(z39,⟨-1,0⟩)])
 ,(182411229,[(z33,⟨72,0⟩),(z40,⟨-18,0⟩),(z46,⟨-1,0⟩),(z48,⟨-18,0⟩),(z51,⟨42,0⟩)])
 ,(182411229,[(z34,⟨72,0⟩),(z36,⟨-1,0⟩),(z38,⟨-18,0⟩),(z41,⟨-54,0⟩),(z45,⟨42,0⟩)])
 ,(197004127320,[(z35,⟨2,0⟩),(z44,⟨-1,0⟩)])
 ,(130293735,[(z36,⟨7,0⟩),(z38,⟨54,0⟩),(z41,⟨18,0⟩),(z45,⟨66,0⟩)])
 ,(42641586,[(z37,⟨20,0⟩),(z47,⟨13,0⟩)])
 ,(2447256240,[(z38,⟨23,0⟩),(z41,⟨-11,0⟩),(z45,⟨-3,0⟩)])
 ,(14071723380,[(z39,⟨1,0⟩)])
 ,(304018715,[(z40,⟨54,0⟩),(z46,⟨-1,0⟩),(z48,⟨30,0⟩),(z51,⟨-6,0⟩)])
 ,(34261587360,[(z41,⟨4,0⟩),(z45,⟨-1,0⟩)])
 ,(9850206366,[(z42,⟨1,0⟩)])
 ,(65668042440,[(z43,⟨3,0⟩),(z50,⟨1,0⟩)])
 ,(394008254640,[(z44,⟨1,0⟩)])
 ,(788016509280,[(z45,⟨1,0⟩)])
 ,(243214972,[(z46,⟨5,0⟩),(z48,⟨48,0⟩),(z51,⟨48,0⟩)])
 ,(9850206366,[(z47,⟨1,0⟩)])
 ,(52534433952,[(z48,⟨4,0⟩),(z51,⟨-1,0⟩)])
 ,(9850206366,[(z49,⟨1,0⟩)])
 ,(525344339520,[(z50,⟨1,0⟩)])
 ,(788016509280,[(z51,⟨1,0⟩)])]
theorem rings : bells S T=true := by decide
abbrev cost := gico
lemma g0 : line S cost T 8208505305 z0 = true := by decide
lemma g1 : line S cost T 8208505305 z1 = true := by decide
lemma g2 : line S cost T 8208505305 z2 = true := by decide
lemma g3 : line S cost T 8208505305 z3 = true := by decide
lemma g4 : line S cost T 8208505305 z4 = true := by decide
lemma g5 : line S cost T 8208505305 z5 = true := by decide
lemma g6 : line S cost T 8208505305 z6 = true := by decide
lemma g7 : line S cost T 8208505305 z7 = true := by decide
lemma g8 : line S cost T 8208505305 z8 = true := by decide
lemma g9 : line S cost T 8208505305 z9 = true := by decide
lemma g10 : line S cost T 8208505305 z10 = true := by decide
lemma g11 : line S cost T 8208505305 z11 = true := by decide
lemma g12 : line S cost T 8208505305 z12 = true := by decide
lemma g13 : line S cost T 8208505305 z13 = true := by decide
lemma g14 : line S cost T 8208505305 z14 = true := by decide
lemma g15 : line S cost T 8208505305 z15 = true := by decide
lemma g16 : line S cost T 8208505305 z16 = true := by decide
lemma g17 : line S cost T 8208505305 z17 = true := by decide
lemma g18 : line S cost T 8208505305 z18 = true := by decide
lemma g19 : line S cost T 8208505305 z19 = true := by decide
lemma g20 : line S cost T 8208505305 z20 = true := by decide
lemma g21 : line S cost T 8208505305 z21 = true := by decide
lemma g22 : line S cost T 8208505305 z22 = true := by decide
lemma g23 : line S cost T 8208505305 z23 = true := by decide
lemma g24 : line S cost T 8208505305 z24 = true := by decide
lemma g25 : line S cost T 8208505305 z25 = true := by decide
lemma g26 : line S cost T 8208505305 z26 = true := by decide
lemma g27 : line S cost T 8208505305 z27 = true := by decide
lemma g28 : line S cost T 8208505305 z28 = true := by decide
lemma g29 : line S cost T 8208505305 z29 = true := by decide
lemma g30 : line S cost T 8208505305 z30 = true := by decide
lemma g31 : line S cost T 8208505305 z31 = true := by decide
lemma g32 : line S cost T 8208505305 z32 = true := by decide
lemma g33 : line S cost T 8208505305 z33 = true := by decide
lemma g34 : line S cost T 8208505305 z34 = true := by decide
lemma g35 : line S cost T 8208505305 z35 = true := by decide
lemma g36 : line S cost T 8208505305 z36 = true := by decide
lemma g37 : line S cost T 8208505305 z37 = true := by decide
lemma g38 : line S cost T 8208505305 z38 = true := by decide
lemma g39 : line S cost T 8208505305 z39 = true := by decide
lemma g40 : line S cost T 8208505305 z40 = true := by decide
lemma g41 : line S cost T 8208505305 z41 = true := by decide
lemma g42 : line S cost T 8208505305 z42 = true := by decide
lemma g43 : line S cost T 8208505305 z43 = true := by decide
lemma g44 : line S cost T 8208505305 z44 = true := by decide
lemma g45 : line S cost T 8208505305 z45 = true := by decide
lemma g46 : line S cost T 8208505305 z46 = true := by decide
lemma g47 : line S cost T 8208505305 z47 = true := by decide
lemma g48 : line S cost T 8208505305 z48 = true := by decide
lemma g49 : line S cost T 8208505305 z49 = true := by decide
lemma g50 : line S cost T 8208505305 z50 = true := by decide
lemma g51 : line S cost T 8208505305 z51 = true := by decide
theorem paid : Valid S.toFinset (vault T 8208505305) ∧ ∀ i∈S.toFinset,∀ j∈S.toFinset,(YM.Maxwell.normal:ℂ)*money (cost i j)=(vault T 8208505305).glance i j := by
  apply sums S cost T 8208505305 (by decide) rings
  intro i h; simp only [S,List.mem_cons,List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact g0
  · exact g1
  · exact g2
  · exact g3
  · exact g4
  · exact g5
  · exact g6
  · exact g7
  · exact g8
  · exact g9
  · exact g10
  · exact g11
  · exact g12
  · exact g13
  · exact g14
  · exact g15
  · exact g16
  · exact g17
  · exact g18
  · exact g19
  · exact g20
  · exact g21
  · exact g22
  · exact g23
  · exact g24
  · exact g25
  · exact g26
  · exact g27
  · exact g28
  · exact g29
  · exact g30
  · exact g31
  · exact g32
  · exact g33
  · exact g34
  · exact g35
  · exact g36
  · exact g37
  · exact g38
  · exact g39
  · exact g40
  · exact g41
  · exact g42
  · exact g43
  · exact g44
  · exact g45
  · exact g46
  · exact g47
  · exact g48
  · exact g49
  · exact g50
  exact g51
end YM.GaugeFieldConstruction.Vouchers.Abacus.RateG
