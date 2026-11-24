import GaugeFieldConstruction.Ferment
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedVariables false
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Spire Branch
attribute [local instance] opCStarAlgebra
open Broc Jet Drapes
variable {K b c d r a v e:ℝ}{N m B:Side}{n:ℕ}
local notation "Λ"=>CSide m B
open Floe Tenant Celeb Dial
abbrev ε'_b(B:Side)(r:ℝ):ℝ:= r/feeG (8*B.val)
variable(H:Room B e)
section load
variable {T V: Tag (ku (N:=CSide m B) (a:=d))} {A: Kelp (CSide m B) d→ Op (Model (CSide m B))} {F: MSheet m B}
variable (rΩ:Crown (badge _) T V a c A)(p:0<d) (C:b≥ 0)(D:CiteT K b e B)(bq:0≤a)(hF:∀ x: Pantry m B,∀ o:x∈ Lobby m B e,F x=bills d p A x)
include rΩ C D p H hF bq
lemma MercyK : PutM K 7 e (ε'_b B a) (phiN 7 b d*c) F:=by
 obtain ⟨X,P,t,G,z⟩:=rΩ; let S (i: Stamp m B):=foam _ (8*B.val) i; let Y:=helix Λ; let R:= phiN 7 b d; let q(V: Stamp m B)(i j):=R*P V (Y i) (Y j)
 have hv:0≤R:=by unfold R phiN composeCost; positivity
 let T:= foams _ (mul_pos (by decide : 0<(8:ℕ)) B.property) (Domain m B); let β:= ε'_b B a; have hb:0 ≤ β:=by unfold β ε'_b feeG; positivity
 have hl(V: Stamp m B): TicketM K 7 e (S V) ∅ (bills d p (X V)) (q V):=by
    intro i j; refine ⟨portKa H (t V) p C D i j, fun u=> ?_⟩; have ⟨h,k,l⟩:= (t V|>.expo (Y i) (Y j)).triggered (right_ne_zero_of_mul u); exact ⟨T.plus h, empty_subset _, foam_in _ _ _ k, foam_in _ _ _ l⟩
 obtain ⟨l,P',hL,t',w⟩:= lumpQ _ _ _ hl
 have hp(i j:Single Λ): saleM β l i j≤ saleM a (fun S i j=> R* P S i j) (Y i) (Y j):=by
    rw [t' _ i j]; refine sum_le_sum fun V _=>?_ ; unfold q; by_cases m':P V (Y i) (Y j)=0; simp [m']; apply mul_le_mul_of_nonneg_right _ (mul_nonneg hv ((t V).expo _ _|>.positive));
    have h:= T.band ((t V|>.expo _ _).triggered m').1; exact Real.exp_monotone ((mul_le_mul_of_nonneg_left h hb).trans_eq (Eq.trans (Eq.symm (mul_assoc _ _ _)) (congrArg (· * (V.card:ℝ)) (show β*feeG (8*B.val)=a from div_mul_cancel₀ _ (by unfold feeG; positivity)))))
 let W:= G.funds hv; refine ⟨l,P',hL,⟨W.posP,fun i=>(sum_le_sum (fun j _=>hp i j)).trans ((Equiv.sum_comp Y (fun k=>saleM a _ (Y i) k)).trans_le (W.rows (Y i))),fun i=>(sum_le_sum (fun j _=>hp j i)).trans ((Equiv.sum_comp Y (fun k=> saleM a _ k (Y i))).trans_le (W.cols _))⟩,fun x v=>?_⟩
 rw [←w x,hF x v]; simp_rw [fun A=>bills_eq H (A:=A) p x v]; rw [z (uθ (porter H x v) p)]; exact map_sum (Matrix.reindexAlgEquiv ℂ ℂ Y.symm) _ _
end load
-- actual placements
section conditions
variable {L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}(k:P.roundZ≤(CSide m B).val)
open Brace Fock.Celeb
abbrev TopPX (m B:Side) (j:ℕ):MSheet m B:= fun x=>spar j firstM x.1
abbrev TopCX (m B : Side) : MSheet m B:= fun x=> Bomb x.1 x.2
abbrev TopIX (m B: Side)(j:ℕ): MSheet m B:=fun x=> (stage (TopPX m B j x) (TopCX m B x))⁻¹
abbrev MP (m B:Side):Tenant.IndexK:=⟨_,northZ m B⟩
include k
private lemma atP(U: Pantry m B)(u: U∈Lobby m B e): spar j firstM U.1= portW (helix _).symm (Pmat (MP m B) (porter P.baseY U u)):=frame_init P.topB P.baseY (P.couture k firstM) (lobby_G u).1
private lemma atC(U: Pantry m B)(u: U∈Lobby m B e): TopCX m B U=portW (helix _).symm (Tenant.pairF false (MP m B) (porter P.baseY U u)):= box_T k _ (lobby_G u).1 _ (lobby_G u).2
variable {c' b' : ℝ}
omit k
lemma clusterV (P: Grasp Y B e)(pK:1≤K):∃ A c0 c1 c2:ℝ, 0<A∧ 0≤ c0 ∧ 0 ≤ c1∧0 ≤ c2 ∧∀ m:Side, P.roundZ ≤ (CSide m B).val → PutM K 7 e A c0 (TopPX m B j) ∧ PutM K 7 e A c1 (TopCX m B) ∧ PutM K 7 e A c2 (TopIX m B j):=by
 obtain ⟨a,b,c,ha,hb,hc,F,Z⟩:= Floe.LedgerP.like Floe.σLp (Floe.km false)
 obtain ⟨d,q,z,hd,p,u,W⟩:=Floe.μCp
 obtain ⟨v,S,V⟩:= Staff P.baseY pK; let R:= min a d; let α:= ε'_b B R; have he:0<R:= lt_min ha hd; have hθ: 0<α := by unfold α ε'_b feeG; positivity
 refine ⟨α, phiN 7 v b*c,phiN 7 v b*c,phiN 7 v q*z,hθ,?_,?_,?_,fun m g=>?_⟩
 · unfold phiN composeCost; positivity
 · unfold phiN composeCost; positivity
 · unfold phiN composeCost; positivity
 let l:=MP m B
 refine ⟨MercyK P.baseY ((F l).drop (min_le_left a d)) hb S V he.le (fun x h=> ?_),MercyK P.baseY ((Z l).drop (min_le_left a d)) hb S V he.le (fun x h=>?_), MercyK P.baseY ((W l).drop (min_le_right a d)) p S V he.le (fun x h=>?_)⟩
 · rw [bills_eq P.baseY hb x h]; exact (atP g x h).trans (congrArg (portW (helix _).symm) (comp_j l _).symm)
 · rw [bills_eq P.baseY hb x h]; exact atC g x h|>.trans (congrArg (portW (helix _).symm) (kM_y l _ false).symm)
 rw [bills_eq P.baseY p x h]; let n:= CSide m B; let G:= Pmat l (porter P.baseY x h); let K:= Tenant.pairF false l (porter P.baseY x h); let L:= (helix n).symm; have hz:=lobby_G h
 have hp:IsUnit (stage G K):=(bow_ok (northZ m B) P.baseY hz.1 (r:={0}) hz.2 (stick_in _ (mem_singleton_self _))).2
 change (stage (spar j firstM x.1) (TopCX _ _ x))⁻¹=_; rw [atP g x h,atC g x h,←parkT,←parkV (U:=stage G K) L hp]; exact congrArg (portW (helix _).symm) (mercy_c l _).symm
end conditions
end YM.CF.XGarden
end
