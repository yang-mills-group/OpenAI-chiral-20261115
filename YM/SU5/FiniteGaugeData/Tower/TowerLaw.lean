import YM.SU5.FiniteGaugeData.Tower.Bond
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Public-facing resolution law

One election. All fixed resolution readings concurrently. Real transfer (as
transport of observables, not arbitrary interpolation) on the physical path
and normalization. Filtering according to separations. Includes gauge and
aligned reflections. This is packaged software, with a limiting *operation*
supported on each source box even across overlapping embeddings, not a
promise that means at the next level are independent of period-varying
marks. Conditional physics application toward existence: this buys positivity
for fixed local chiral systems at finite resolutions, on the limiting E of FiniteGaugeData
charged data, and genuine compatibility under the cross-level coarsening.
It does not yet specify a limit-continuum algebra or nonzero interaction
there.
-/
open Fock
section
variable (D:ℕ→Family (tent Y H)→Family (tent Y H))
-- A limiting level transfer, in the indicated presentation. `D` can be
-- applied to BOTH (i) physical singlets in either language and (ii) other
-- even wide tests (useful for estimation). Only defined/claimed on that
-- class. Moves reflection to scaled plane. Separation paid before
-- multiplication (full f itself may include arbitrary overlapping products;
-- only can't separate transform of such factors). observ only gauged.
-- Pointwise algebra no claim closure under ordinary FC star; physical CAR
-- interpretations still those of FiniteGaugeData.
structure Resolution (Z: ℕ→Family (tent Y H)→Family (tent Y H)): Prop where
 supports (s:ℕ){S:Finset Cover}{F:Family (tent Y H)}(p:InTest K true S false F):
   InTest K true (wingspan Λ l S) false (Z s F) ∧ E (s+1) (Z s F)= E s F
 occupation (s:ℕ){S}{F:Family (tent Y H)}(p:F∈ observ K S true): CovCover (tent Y H) (Z s F)
 plus_lift (s:ℕ){F G:Family (tent Y H)}(h:TestFamily K true F)(p:TestFamily K true G):
   Z s (F+G)=Z s F+Z s G
 amp (s:ℕ){F:Family (tent Y H)}(h:TestFamily K true F)(e:ℂ): Z s (e • F)=e • Z s F
 unit (s:ℕ): Z s 1=1
 turn (s:ℕ)(a:Axis)(z:ℤ){f:Family (tent Y H)}(h:TestFamily K true f):Z s (mirror K a z f)=mirror K a (Λ.R.L.val*z) (Z s f)
 separates (s:ℕ){S U}{F G:Family (tent Y H)}(h:InTest K true S false F)(p:InTest K true U false G) (v:separated (2*(Advance.nearZero (aliasLaw Λ)+distanceLaw l)) S U): Z s (F*G)= Z s F * Z s G
-- single map on full hierarchy supports. Here helper proofs use path data;
-- users only need the resulting Resolution.
variable (n k₀:ℕ→ℕ) {q:ℕ→ℕ}(Q : CrimsonLine (i:=i) (k:=k) (I:=I) (E:=E) Y H q) (P:PathLease (i:=i) (k:=k) (q:=q) Y H n k₀)
noncomputable def descend (s:ℕ)(F:Family (tent Y H)):Family (tent Y H) := if h:TestFamily (tent Y H) true F then destined Y H s (i∘q∘n) (k∘k₀) (Classical.choose h.paid) P.members F else 0
local notation "F₀"=> descend Y H n k₀ P
local notation "D₀"=>destined Y H s (i∘q∘n) (k∘k₀)
include V Q
lemma costing {S F}(x:InTest K true S false F):F₀ s F=D₀ S P.members F:=by
 let p:=aux_test x
 unfold descend; rw [dif_pos p]
 let X:Finset Cover:= Classical.choose p.paid
 let Z:= (Classical.choose_spec p.paid)
 calc
    _=D₀ (X∪S) P.members F:= cross_compatible Y H s _ _ P.members Z (growth Y H V n k₀ Q P).tendsto_atTop (legally Y H V n k₀ Q P) subset_union_left
    _=_:= (cross_compatible Y H s _ _ P.members x (growth Y H V n k₀ Q P).tendsto_atTop (legally Y H V n k₀ Q P) subset_union_right).symm

lemma resolution: Resolution Y H (E:=E) (F₀):=by
 let p:=i ∘ q ∘ n; let t:=k ∘ k₀
 have ht:= growth Y H V n k₀ Q P|>.tendsto_atTop
 have hp:= legally Y H V n k₀ Q P
 refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
 · intro s S F x; rw [costing Y H V s n k₀ Q P x]; exact ⟨attaches ..,equality Y H V s n k₀ Q P S x⟩
 · intro s S F e; have h:=((obs_in ..).mp e).1; rw [costing Y H V s n k₀ Q P h]; exact ((obs_in ..).1 (color_stays Y H s e p t P.members)).2
 · intro s F B G h; obtain ⟨S,x'⟩:=G.paid; obtain ⟨U,v'⟩:= h.paid
   have hs:= x'.mono (Finset.subset_union_left (s₂:=U)) -- binder names?
   have hv:InTest K true (S∪U) false B:= v'.mono subset_union_right
   rw [costing Y H V s n k₀ Q P hs,costing Y H V s n k₀ Q P hv,costing Y H V s n k₀ Q P (hs.add hv),Tower.add_one Y H s p t P.members hs hv]
 · intro s F h r; obtain ⟨S,x⟩:=h.paid
   rw [costing Y H V s n k₀ Q P x, costing Y H V s n k₀ Q P (.smul r x),scales_one Y H s p t P.members x]
 · intro s; rw [costing Y H V s n k₀ Q P (InTest.one (S:=∅)),unidad Y H s p t P.members ht hp]
 · intro s a z f h; obtain ⟨S,x⟩:= h.paid
   rw [costing Y H V s n k₀ Q P (axial K a z x), costing Y H V s n k₀ Q P x,both_bands Y H s p t P.members x ht hp a z]
 · intro s S U F h x y C; have G:InTest K true (S∪U) false (F*h):= (x.mono subset_union_left).mul (y.mono subset_union_right)
   rw [costing Y H V s n k₀ Q P x, costing Y H V s n k₀ Q P y,costing Y H V s n k₀ Q P G,parted Y H s p t P.members x ht hp y C]

omit V Q
structure Coherent (D:ℕ→ Family (tent Y H)→ Family (tent Y H)) (a b:ℕ→ℕ) : Prop where
 circuit : Resolution Y H (E:=E) D
 growsA : StrictMono a
 growsB : StrictMono b
 gate(r:ℕ): legacy Y (i (a r)) (k (b r))
 finance (s:ℕ):∀ᶠ r:ℕ in atTop,Ferry Y s (i (a r)) (k (b r))
 implements(s:ℕ)(S:Finset Cover):∃ C:ℝ,0<C∧ ∀ e:ℝ,0< e → ∀ᶠ r in atTop,
      let m:=i (a r); let n:=k (b r)
      ∀ (F:Family (tent Y H)),InTest K true S false F→∀x:ℝ,pay F x→
      let q:=block Y H s m n S F; let W:=toll Y H (s+1) (wingspan Λ l S)
      pay (D s F) (C*x) ∧ pay q (C*x) ∧ pay (q-D s F) (e*x) ∧ sharp Y H (s+1) m n q=sharp Y H s m n F ∧
      ‖sharp Y H s m n F-E s F‖≤ e*x∧ ‖sharp Y H (s+1) m n q-sharp Y H (s+1) m n (D s F)‖≤ W*(e*x)
include V Q
lemma ethic: Coherent (i:=i) (k:=k) Y H (E:=E) (F₀) (q∘n) k₀ :=by
 let f:=i∘q∘n; let t:=k∘k₀
 refine ⟨resolution Y H V n k₀ Q P, Q.grows.comp P.periods,P.cutters,P.gate, fun s=>(license Y H V n k₀ Q P s),?_⟩
 intro s S
 let A:=wingspan Λ l S
 let R:=toll Y H (s+1) A
 let m(r):= f r; let w(r):= t r
 obtain ⟨C,p,c⟩:=operator_paid Y H s f t P.members S
 have Hn:=P.periods.tendsto_atTop; have Hm: Tendsto f atTop atTop:= V.pick.grow_i.tendsto_atTop.comp (Q.grows.tendsto_atTop.comp Hn)
 have Hk: Tendsto t atTop atTop := V.pick.grow_k.tendsto_atTop.comp P.cutters.tendsto_atTop
 have hr:=toll_pays Y H (s+1) A
 refine ⟨C,p,fun e h=>?_⟩
 have hf :Tendsto (fun r:ℕ=>(1/2:ℝ)^r) atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
 filter_upwards [c,Cresc.outfits Y H s f t S P.members e h,Hn.eventually (Q.budget s S),Hn.eventually (hf.eventually (ge_mem_nhds h)),
    (Hm.eventually (turning Y H (s+1) A)),license Y H V n k₀ Q P (s+1), Hk.eventually hr.2] with i J u B D' F' μ Z₀
 intro v₁ v₂ F x y G
 have ht:=costing Y H V s n k₀ Q P x
 let v:=block Y H s (m i) (w i) S F
 have hp:= J F x y G; have hw:=u F x y G; have H₂:= (B.2.2 F x y (G _)).2 (k₀ i) (P.gate i)
 simp_rw [ht]; refine ⟨hp.1,hp.2,hw,upper_coupling Y H s S (m i) (w i) ⟨μ.depth,μ.enters⟩ x F',H₂.trans (mul_le_mul_of_nonneg_right (show _ from D') (pay_nonneg G)),?_⟩
 have μ0:Ferry Y (s+1) v₁ v₂:= μ
 change ‖sharp Y H (s+1) v₁ v₂ (block Y H s v₁ v₂ S F)-sharp Y H (s+1) v₁ v₂ (destined Y H s f t S P.members F)‖≤_
 rw [←sharp_sub Y H (s+1) (x:=aux_test (booked Y H s v₁ v₂ S F)) (u:=aux_test (attaches Y H s f t S P.members F)) μ0]
 exact Z₀ _ μ.depth _ (InTest.subOp (booked ..) (attaches ..)) _ (hw _)

-- public application song. preserve original election property; no Printed
-- used on D. Packed criterion for Bill via Tower Wanted includes #print in Diagnostic.
lemma buy_exists: ∃ (D:ℕ→Family (tent Y H)→Family (tent Y H))(a b:ℕ→ℕ), Coherent (i:=i) (k:=k) Y H (E:=E) D a b:=by obtain ⟨n,k,w⟩:= permits Y H V Q; exact ⟨_,_,_,ethic Y H V n k Q w⟩
omit V Q
lemma solstice(ε:ℝ):
    ∃ (Λ:Preparation)(l:ℕ), ε < Λ.x ∧ Λ.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (h:Real.exp 1 ≤ Λ.x),∃ (Y : Course Λ (VolumeCape.Dream.Nimbus l)),
        (∃ z, Usable (D:=Λ.δ) Λ.V Λ.W Λ.J Λ.N0 z Λ.delay Y.meter) ∧
        (∀ i k, ((Y.voyage i).X k).Prepared Λ.P Λ.delay) ∧
        (∀ i j:ℕ, Advance.LoomLaw ((Y.voyage i).CapeT j) (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot l).C)) ∧
        ∃ u π:ℕ→ℕ, StrictMono u ∧ StrictMono π ∧ Nonempty (Y.Query u π) ∧
          ∃ i k I E, StrictMono i ∧ StrictMono k ∧ Universal Y h (u∘i) (π∘k) I E ∧
            ∃ (D:ℕ→Family (tent Y h)→Family (tent Y h))(q a b:ℕ→ℕ), CrimsonLine Y h (i:=u∘i) (k:=π∘k) (I:=I) (E:=E) q ∧ Coherent Y h (i:=u∘i) (k:=π∘k) (E:=E) D (q∘a) b∧ StrictMono a :=by
 obtain ⟨Λ,l,v,t,h,Y,p₁,p₂,p₃,u,π,a,b,p,i,k,I,E,c,d,V,_⟩:=diamond ε
 obtain ⟨q,Q⟩:=purchase_line Y h V
 obtain ⟨n,k',P⟩:=permits Y h V Q
 refine ⟨Λ,l,v,t,h,Y,p₁,p₂,p₃,u,π,a,b,p,i,k,I,E,c,d,V,_,q,n,k',Q,ethic Y h V n k' Q P,P.periods⟩
end
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.solstice
