import YM.CF.Graph.Mars
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
open MeasureTheory Cascade Vale CF.Paige Vault Nova
open Emu Flare
variable {α:Type*}{m B L:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e v b c a l r K u η vA k s r' D L' C μ y R w z:ℝ}{P:Grasp Y B e}{hP:Pearl P}
variable (V:GramM (mid m B))(S:Loom (mid m B))
variable (Q: Pic.Span hP K b v c l r' n)(H:SkinT V S e)
def adjustX(R:GramM N)(T:Orbit N):ℝ:= R.path.inChannels R.funds R.p R.beta T.1
def recX (P:Grasp Y B e)(A:GramM (mid m B))(S:Loom (mid m B))(V:Orbit (mid m B)): Phys (mid m B):= Complex.exp (-A.v) • denZ A P S V
abbrev recW (O:Opt (α:=α) (mid m B))(P:Grasp Y B e)(A:GramM (mid m B))(S:Loom (mid m B))(V:Orbit (mid m B)):=feel O V.1 (recX P A S V)
abbrev baseW (O:Opt (α:=α) (mid m B))(P:Grasp Y B e)(A:GramM (mid m B))(S:Loom (mid m B))(V:Orbit (mid m B)):= dim A V • feel O V.1 (cab A P S V)
lemma porch(T:Orbit (mid m B)): recX P V S T=past V T.1 • beam V P S T:=by
 unfold recX; rw [mote, smul_smul, ←Complex.exp_add, show -V.v+_=(-(V.path.inChannels V.funds V.p V.beta T.1):ℝ) from ?_,← Complex.ofReal_exp]; apply Eq.symm (RCLike.real_smul_eq_coe_smul _ _)
 unfold GramM.H0; push_cast; ring
lemma feel_r(U: Opt (α:=α) N)(V:Pane N)(p q:Phys N)(r:ℝ): feel U V (r • p)=r • feel U V p∧ feel U V (p-q)=feel U V p -feel U V q:=by
 unfold feel valA; simp only [map_sub, inner_sub_right]; refine ⟨?_,True.intro⟩; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul, inner_smul_right]; rfl -- tune
omit H Q
include H Q
lemma pall_b (T:Orbit (mid m B))(O:Opt (α:=α) (mid m B))(h:n ≤ (mid m B).val)(hYA:T∈ Lace V)(B':Ledger R u η r C V)(Z:HelpP T.1 vA r)(t:0≤vA)(a:0≤r)(hP:0≤R)(k':0≤k)(hC:0≤C)(hp:‖Emu.gain O.R‖ ≤ (mid m B).val^2)(w: Gall.Yep k (mateK (mid m B)) (changeM (m:=m) P T.1 V.J.M) (y*Kea.angel m P V.J.M))(hy:0≤y)(l:∀ i:LeanV (Single (mid m B)),Pays k (drawT (spar j V.J.M T.1) i) R)(h₀:pittance (mid m B) vA C ≤1): let z:= baton (mid m B) u vA C k
    ‖recW O P V S T-baseW O P V S T‖ ≤ dim V T *(z*(y*Kea.angel m P V.J.M) *feeP O k) :=by
 intro z; have hr:S T=T.1:=H.high T hYA; obtain ⟨i,f,p⟩:= H.wave; have hx:= (P.broadness _ (Q.plan m h).1 V.J.M).projection (S T) (p.paid T); let N:=mid m B; let A:= mile j V S T
 have hu:= ridge B' T (show HelpP (S T) vA r from Eq.mpr (congrArg (fun f=>HelpP f vA r) hr) Z) t a hP k' hC hx (show flags _ _=_ from hYA) h₀ (fun i=> by rw [hr]; exact l i)
 let X:= cab V P S T; let U:= beam V P S T; have he:U-X=acts (A-1) X:=by rw [act_sub,act_one]; rfl
 let b:= y*Kea.angel m P V.J.M; have hb:0≤b:= mul_nonneg hy ((Kea.angel_p ‹Pearl P› Q.stmt (Q.plan _ h).1 Q.p Q.eP V.J.M (Q.plan _ h).2).le) -- tune hP shadow
 have hh:= hu.2 _ _ _ hb (show Gall.Yep k (mateK _) X b from (by unfold X cab; rw [hr]; exact w)); have hD:0 ≤past V T.1:= (Real.exp_pos _).le
 unfold baseW recW; rw [porch,(feel_r O _ _ X _).1,Graph.dim,Set.indicator_of_mem hYA,←smul_sub,← (feel_r O T.1 U X 0).2,norm_smul]; rw [show ‖past V T.1‖=past V T.1 from Real.norm_of_nonneg hD,he]; exact mul_le_mul_of_nonneg_left (bear O T.1 _ hp hh (mul_nonneg hu.1 hb) k') hD
lemma road_b (T:Orbit (mid m B))(O:Opt (α:=α) (mid m B))(h:n ≤ (mid m B).val)(hYA:T∉ Lace V)(B':Ledger R u η r C V)(a:0≤r)(hP:1≤R)(hC:0≤C)(hp:‖Emu.gain O.R‖ ≤ (mid m B).val^2)(g: V.path.Bounds V.funds μ D L')(hv:0≤V.beta)(hw:0≤w)(vL:w≤V.funds.linear): let N:=mid m B
    ‖recW O P V S T-baseW O P V S T‖ ≤ lite O *Real.exp (flagT N u η C-kinetic (More N) V.p D L' V.beta w) :=by
 intro N; obtain ⟨v,k,F⟩:=H.wave; have hh:= (P.broadness _ (Q.plan m h).1 V.J.M).projection (S T) (F.paid T); let A:=past V T.1; let X:= lite O; let f:= flagT N u η C; have ht:0 ≤ X:=by unfold X lite; positivity; -- tune
 have he:0≤A:=(Real.exp_pos _).le; let P':= cab V P S T; have hg:‖P'‖=1:=(sea_g (Q.plan m h).1 (S T) (F.paid T) V.J.M).2; have hu:‖beam V P S T‖ ≤ Real.exp f:= (spentS _ _ P').trans (by rw [hg,mul_one]; exact stout B' _ a hP hC hh)
 let x:= kinetic (More N) V.p D L' V.beta w; have hs:A≤Real.exp (-x):= Real.exp_le_exp.mpr (neg_le_neg (fullH g V.p T.1 hw vL hv hYA)); unfold baseW recW; rw [dim,Set.indicator_of_notMem hYA,zero_smul,sub_zero,porch,(feel_r O _ _ P' _).1,norm_smul]; change ‖A‖*_ ≤ X*Real.exp (f-x); rw [Real.norm_of_nonneg he]; exact (mul_le_mul hs ((earn O _ _ hp).trans (mul_le_mul_of_nonneg_left hu ht)) (norm_nonneg _) (he.trans hs)).trans_eq (by rw [sub_eq_add_neg,Real.exp_add]; ring)
end YM.CF.Graph
