import Zephyr.Chern.Garnet
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern

open YM YM.Lattice YM.CF YM.CF.Tulip YM.Laurent Filter


variable {a e B W r:ℝ}{N:Side}{F:Oil N}
def rootAt (N:Side)(x:Cover):= Cube.node (wrap N x)

def Holds (u:Finset (Band N)) (m:ℕ):Prop :=
  ∀ S,S.card<m→ S∈u

lemma Bough.solo (t:Bough e a r F): Solo a r F e :=
  ⟨fun S x=>t.f S x.val,t.c,t.pie,t.led,fun x=>t.shows _ x.property⟩
lemma Bough.sprig (t:Bough e a r F)(d:0<e)(z:Finset (Band N))(A:StemA N)(x:Cover):
    Bloom (Zephyr.Chern.sprig (t.sift z) A x)
      (∑ i:IS,wad (t.sift z) A (tag N x i) (tag N x i)) :=
  Bloom.sum _ fun _ _=> ((t.sift_drip z _ _ _ d).1).bloom

/-- Uniform angular-direction tails, even though stream grows off bounded sets with N.
Cardinality cutoff; the retained diagonal here needs only radius m around the site
(and one can use *any* angular support cutoff retaining those words there). -/
lemma padded_error (t:Bough e a r F)
    (A:StemA N)(x:Cover)(h:Temper (rootAt N x) A B)(w:Oily a e B W)
    {z:Finset (Band N)} {m:ℕ}(p:Holds z m)(k:Fin 3):
    ‖bud (sprig F A x) k-bud (sprig (t.sift z) A x) k‖ ≤
      Fintype.card IS * (W*r*Real.exp (-(a/2)*m)) := by
  rw [(solo_sprig t.solo w.s.ready A x).bud_eq,(t.sprig w.s.ready ..).bud_eq]
  rw [Finset.sum_apply,Finset.sum_apply,←Finset.sum_sub_distrib]
  apply le_trans (norm_sum_le ..)
  exact (Finset.sum_le_sum
    (fun i (_:i∈Finset.univ)=> t.error (i:=tag N x i) (j:=tag N x i) w h
      (Or.inl rfl) z m p k)).trans (by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul])

def breadth (x:Cover):ℝ:=16*((1:ℝ)+size ((2:ℕ) • x))

lemma deep_grace (x:Cover): Temper (rootAt N x) (stream N) (breadth x):= by
  have h:separation 1 (rootAt N x)≤size ((2:ℕ) • x):=by
    rw [separation_comm,rootAt,node_wrap,separation,add_sub_cancel_right]
    exact pdist_wrap ..
  exact (stream_mild N).slide h

lemma sunset (x:Cover) (ha:0<a)(he:0<e)(r:ℝ)
    (d:ℝ)(hd:0<d) :
    ∃ m,∀ {N:Side} {F:Oil N} (t:Bough e a r F) {z:Finset (Band N)}, Holds z m→
      ∀ k,‖bud (sprig F (stream N) x) k-bud (sprig (t.sift z) (stream N) x) k‖ < d:=by
  obtain ⟨W,⟨w⟩⟩:=oily ha he (breadth x)
  have g:= ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Tendsto.const_mul_atTop (half_pos ha)
     tendsto_natCast_atTop_atTop)).const_mul (W*r)).const_mul (Fintype.card IS:ℝ)
  simp only [Function.comp_def,mul_zero,←neg_mul] at g
  obtain ⟨m,u⟩:= (g.eventually (gt_mem_nhds hd)).exists
  exact ⟨m, fun t _ p k=>lt_of_le_of_lt (padded_error t _ x (deep_grace x) w p k) u⟩

theorem tiled_flux {s:ℕ}(hs:1≤s)(x:Cover)
    (ha:0<a)(he:0<e)(r:ℝ):
    ∃ d:ℝ, 0<d∧ ∃ m v,∀ {N:Side},v≤N.val→∀ {M:Male}
      (t:Bough e a r (funde s M N)) {z:Finset (Band N)}, Holds z m →
      Bud (sprig (t.sift z) (stream N) x) ∧
      d < (bud (sprig (t.sift z) (stream N) x) 2).re:=by
  obtain ⟨δ,d,w,P⟩:=deep_flux hs x
  obtain ⟨m,j⟩:=sunset x ha he r _ (half_pos d)
  refine ⟨δ/2,half_pos d,m,w,?_⟩
  intro N h M t z hz
  refine ⟨(t.sprig he z (stream N) x).1,?_⟩
  have u:=(Complex.re_le_norm ..).trans_lt (j t hz 2)
  rw [Complex.sub_re] at u
  linarith [P h M]
