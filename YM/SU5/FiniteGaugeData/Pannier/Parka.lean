import YM.SU5.FiniteGaugeData.Pannier.Blizzard
/-! # Send good tile charges in their frames.
included region cheap, others far (quantity independent of total number). -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {R ε:ℝ}
section
variable {ι:Type*}[LinearOrder ι][Fintype ι][Nonempty ι]
variable {s S D:Finset ι}{x y:Ket ι}{P Q: Op ι}
lemma pad_com : cutM S* Fock.padded S P=Fock.padded S P*cutM S:=by
 unfold Fock.padded; rw [mul_add,←mul_assoc,←mul_assoc,(cutM_idp _).isIdempotentElem, add_mul,mul_assoc,_root_.mul_sub, _root_.sub_mul,mul_one,one_mul,(cutM_idp _).isIdempotentElem]; rw [mul_assoc,mul_assoc,(cutM_idp _).isIdempotentElem]
-- use on arbitrary history bound
private lemma gate_cost {R v:ℝ}(h:‖P‖≤R) (hp:‖x‖≤v):‖acts P x‖≤R*v:= (Flare.opy ..).trans (mul_le_mul h hp (norm_nonneg _) ((norm_nonneg _).trans h))
lemma shore_cost (p:IsStarProjection P)(x:Ket ι): ‖acts P x‖ ≤ ‖x‖:= (Flare.opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) (p.norm_le _))
lemma leases (h:IsUnit (Fock.padded S P))(p:withinM S x) : withinM S (acts (Fock.padded S P)⁻¹ x):=by
 let P':= Fock.padded S P; have e:IsUnit P':=h; let s:= cutM S
 have ht: s*P'⁻¹=P'⁻¹*s:=by
    nth_rw 1 [←one_mul s,←(live e).2,mul_assoc _ P',←show s*P'=P'*s from pad_com]; rw [mul_assoc,mul_assoc,(live e).1,mul_one] -- tune
 unfold withinM; change acts s _=_; rw [←act_mul,ht,act_mul,p]
def warmth (P:Op ι)(S:Finset ι)(x:Ket ι):= acts P (acts (Fock.padded S P)⁻¹ x)
lemma warm_cost (S:Finset ι)(h:IsStarProjection P)(p:‖(Fock.padded S P)⁻¹‖≤ R)(t:‖x‖≤1) : ‖warmth P S x‖≤ R:= ((shore_cost h _).trans (gate_cost p t)).trans_eq (mul_one _)
lemma warmed (h:IsUnit (Fock.padded S P))(p:withinM S x) : acts (cutM S) (warmth P S x)=x := by
 let v:= acts (Fock.padded S P)⁻¹ x; have he:=leases h p
 have hp: acts (Fock.padded S P) v=x:= (act_mul ..).symm.trans (by rw [(live h).1,act_one]); have ht:withinM S v:=he
 rw [Fock.padded,act_add,act_mul,act_sub,act_one,ht,sub_self,add_zero,act_mul] at hp; exact hp
lemma warmed_contact (h:IsUnit (Fock.padded S P))(p:withinM S x)(u:withinM S y): inner ℂ (warmth P S x) y=inner ℂ x y := by
 nth_rw 1 [←u]; rw [← act_inner,(cutM_idp _).isSelfAdjoint, warmed h p]
lemma server_sh (q:IsStarProjection P)(x:Ket ι): trim P (warmth P S x):=by unfold trim warmth; rw [←act_mul,q.isIdempotentElem]
def sparkUp (Q:Op ι)(S D:Finset ι)(x:Ket ι):= acts (cutM D) (warmth Q S x)
lemma covers_spark : withinM D (sparkUp Q S D x):= by unfold withinM sparkUp; rw [←act_mul,(cutM_idp _).isIdempotentElem]
lemma touch_spark (g:IsUnit (Fock.padded S P))(t:S⊆D)(p:withinM S x) : acts (cutM S) (sparkUp P S D x)=x:= by rw [sparkUp,←act_mul,cut_from_left _ _ t]; exact warmed g p
lemma spark_gap (h: ‖(Fock.padded s P)⁻¹‖≤ R)(p:withinM s x)(u:IsUnit (Fock.padded s P))(q:‖cutM (Dᶜ)*P*cutM s‖ ≤ ε)(t:‖x‖≤1) : ‖warmth P s x - sparkUp P s D x‖≤ε*R:=by
 let v:= acts (Fock.padded s P)⁻¹ x; have ht:withinM s v:= leases u p
 have hx: acts (cutM Dᶜ*P*cutM s) v= warmth P s x-sparkUp P s D x:=by rw [act_mul,ht,act_mul,dim_cut,act_sub,act_one]; rfl
 rw [←hx]; exact gate_cost q ((gate_cost h t).trans_eq (mul_one _))
lemma pserve (u:withinM s x)(v:s⊆ S): (acts (Fock.padded S P) x)= acts (cutM S) (acts P x):=by
 have h:=within_more u v; rw [Fock.padded, act_add,act_mul,act_mul,act_sub,act_one,h,sub_self,add_zero]

-- Compare exact matrix on a larger set S to data from one well(tile basis). no adjoints needed.
private lemma upgrade (p:s⊆S) (u:‖(P-Q)*cutM S‖≤ε) (e:‖cutM (S \ s)*Q*cutM s‖≤ε) (hp:IsUnit (Fock.padded S P))(hq:IsUnit (Fock.padded s Q))(g:‖(Fock.padded S P)⁻¹‖ ≤ 2*R)(r:‖(Fock.padded s Q)⁻¹‖ ≤ R) (l:withinM s x)(t:‖x‖ ≤ 1):
    ‖acts (Fock.padded S P)⁻¹ x-acts (Fock.padded s Q)⁻¹ x‖≤ 2*R*(ε*R+ε*R):=by
 let P':=Fock.padded S P; let Q':=Fock.padded s Q; let V:=acts Q'⁻¹ x; have h: withinM s V:= leases hq l; have hV:‖V‖≤ R:=(gate_cost r t).trans_eq (mul_one _)
 have ht: acts Q' V=x:=(act_mul ..).symm.trans (by change acts (Q'*Q'⁻¹) _=_; rw [(live (show IsUnit Q' from hq)).1,act_one])
 let X:= acts (P-Q) V; let Y:= acts (cutM (S \ s)*Q*cutM s) V; have hX:‖X‖≤ε*R:=by unfold X; rw [show acts (P-Q) V = acts ((P-Q)*cutM S) V by rw [act_mul,within_more h p]]; exact gate_cost u hV
 have he: acts P' V-acts Q' V=acts (cutM S) X+ Y:=by
    rw [pserve h p,pserve h (subset_refl s)]; unfold X Y; rw [act_sub,act_mul,h,cut_less p,act_mul,act_sub,map_sub]; abel
 have hA:‖x - acts P' V‖ ≤ ε*R+ε*R:=by
    rw [norm_sub_rev, ← ht,he]; exact (norm_add_le ..).trans (add_le_add ((shore_cost (cutM_idp _) _).trans hX) (gate_cost e hV))
 change ‖acts P'⁻¹ x-V‖ ≤_; rw [show acts P'⁻¹ x-V=acts P'⁻¹ (x-acts P' V) by rw [map_sub,←act_mul,(live (show IsUnit P' from hp)).2,act_one]]; exact gate_cost g hA
-- heat drop on removing other Sparse sets; preserve projections (orientation-specific). includes local truncate.
lemma upgraded (p:s ⊆ S) (u:‖(P-Q)*cutM S‖≤ε) (e:‖cutM (S \ s)*Q*cutM s‖≤ε) (w:‖cutM (Dᶜ)*Q*cutM s‖ ≤ε)(hp:IsUnit (Fock.padded S P))(hq:IsUnit (Fock.padded s Q))(g:‖(Fock.padded S P)⁻¹‖ ≤ 2*R)(r:‖(Fock.padded s Q)⁻¹‖ ≤ R) (l:withinM s x)(t:‖x‖ ≤ 1)(k:IsStarProjection P):
    ‖sparkUp Q s D x-warmth P S x‖≤ ε*(2*R+4*R*R):=by
 let X:= acts (Fock.padded S P)⁻¹ x; let Y:= acts (Fock.padded s Q)⁻¹ x; let U:=acts (P-Q) Y; let V:=acts P (X-Y); let L:= warmth Q s x; let L':=warmth P S x
 have he:‖Y‖≤R:= (gate_cost r t).trans_eq (mul_one _)
 have hY:withinM s Y:= leases hq l
 have v:‖U‖ ≤ ε*R:=by unfold U; rw [show acts (P-Q) Y=acts ((P-Q)*cutM S) Y by rw [act_mul,within_more hY p]]; exact gate_cost u he
 have hV:‖V‖ ≤ 2*R*(ε*R+ε*R):= (shore_cost k _).trans (upgrade p u e hp hq g r l t)
 have hs:L'-L=U+V:=by unfold U V; change acts P X-acts Q Y= _; rw [act_sub,map_sub]; abel
 rw [norm_sub_rev]; change ‖L'- _‖≤ _; apply (norm_sub_le_norm_sub_add_norm_sub L' L (sparkUp ..)).trans; rw [hs]
 exact (add_le_add ((norm_add_le ..).trans (add_le_add v hV)) (spark_gap r l hq w t)).trans_eq (by ring)

end
variable {M:Tulip.Male}{n:Side}{U:Pane n}{S s D:Finset (Seat n)}{b:Bool}{d:ℕ}{γ δ:ℝ}{x:Ket (Single n)}{j:ℕ}
lemma parcel_spark (p:Winter j δ n γ d ε)(u:0≤δ)(g:Guard U δ)(hx:Rightful (Lattice.halo d S) U 1 γ)(q:HearthB R (sp b j M (1:Pane n)) S)(h:HearthB R (sp b j M (1:Pane n)) s)
    (he:s⊆ S)(e:Distant d (S \ s) s)(w:Distant d (Dᶜ) s)(t:ε*R≤1/3)(Z:IsStarProjection (sp b j M U))(hp:withinM (modesIn n s) x)(hq:‖x‖≤1) :
    ‖sparkUp (sp b j M (1:Pane n)) (modesIn n s) (modesIn n D) x -warmth (sp b j M U) (modesIn n S) x‖ ≤ ε*(2*R+4*R*R):=by
 have hb: ‖(sp b j M U-sp b j M (1:Pane n))*Vo S‖≤ε:= hearthB_wind p u g hx; have hR:= hearthB_stands q hb t
 refine upgraded (modes_monotone he) hb ?_ ?_ hR.1 h.1 hR.2 h.2 hp hq Z
 · rw [show modesIn n S \ modesIn n s=modesIn n (S \ s) from ?_]; exact hearthB_cross p b M (guard0 u) e; ext; simp
 rw [show (modesIn n D)ᶜ=modesIn n Dᶜ from ?_]; exact hearthB_cross p b M (guard0 u) w; ext; simp
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.parcel_spark
