import YM.CF.Proa.Plan
set_option autoImplicit false
noncomputable section
namespace YM.CF.Proa
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Phase Spire
set_option synthInstance.maxSize 8000
variable {ι J:Type*} {n:Type*}[LinearOrder n][Fintype n]
lemma moves (P C:Op n)(h:IsStarProjection P)(g:TagG P C)(i: Cod n):Commute (exp (dg C)) (cry P i):=by
 rw [tallied C g.nil]; cases i with| mk u k=>
    let v:= basisKet k
    cases u
    · change quant _ *seekF _ _= seekF _ _ *quant _; rw [seekF,prong_p,quant_create,←act_mul,add_mul,one_mul,mul_sub,g.2,mul_one,sub_self,add_zero] -- order
    change quant _* hideF _ _ = hideF _ _ *quant _; rw [hideF,prong_t,quant_ann,←act_mul,star_add,add_mul,star_one,one_mul, show star C * P=0 by nth_rw 1 [←h.isSelfAdjoint]; rw [←star_mul,g.1,star_zero],add_zero]
lemma rentF (P A C:Op n)(h:IsStarProjection P)(g:TagG P A)(v:TagG P C): TagG P (A-C)∧ exp (dg A)=exp (dg C)*exp (dg (A-C)):=by
 have ht:TagG P (A-C):=by refine ⟨by rw [mul_sub,g.1,v.1,sub_self],by rw [sub_mul,g.2,v.2]⟩
 refine ⟨ht,?_⟩; have hk:C*(A-C)=0:=by nth_rw 1 [←v.2]; rw [mul_assoc,ht.1,mul_zero]
 rw [tallied _ ht.nil,tallied _ v.nil,tallied _ g.nil,←quant_mul]; congr 1; simp only [mul_add,add_mul,mul_one,one_mul,hk]; abel
lemma rams {A C:Op n}(u:IsStarProjection A)(v:TagG A C)(f:ι→ Bool)(P:ι→n→ℂ)(l:List ι): Commute (exp (dg C)) (rollC (fun i=> ∑ j,P i j • cry A (f i,j)) l):=by
 induction l with
 | nil=> simp only [rollC,List.map_nil,List.prod_nil]; exact Commute.one_right _
 | cons i l ih=>simp only [rollC,List.map_cons,List.prod_cons]; exact (Commute.sum_right _ _ _ (fun j _=> (moves _ _ u v (f i,j)).smul_right (P i j))).mul_right ih -- tune

variable {L N Q B:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ} {P:Grasp Y B e}(he:0<e)
variable (G:Ratio (CSide N B) (CSide Q B))(hk:G.count=L)(w:P.roundZ ≤ (CSide N B).val)(A:Aim (CSide Q B))(M:Male)(x:nomA N Q B)(p:JointB G x e)
variable (C:Op (Single (CSide N B)))
include he hk w p
lemma token (F:Letter ι (Iota G))(D:List ι) : let α:=foal j true M G (unionP x); let β:=wh j L ho true M G (unionP x); let Y:=spar j (upMale L ho M) x.2; let V:=ticketT (Thread j) true M G (unionP x); let U:=ticketT (Thread j) false M G (unionP x); let Z:=Kennel.capT α (foot G (A.den x.1)); let H:=traitP β (pine j L ho (Thread j) true M G (unionP x)) V Z; let W:=fruit L j ho G M x Z
 TagG Y C → ‖desire L j ho G M x Z‖<1 → TagG Y (W-C) ∧
 fire (Thread j) G M (unionP x) (acts (rollC (dialL F) D) (acts (exp (dg Z)) (graft G P x.1 M))) = (Complex.exp (altar G P x M+invoice (desire L j ho G M x Z))) • (
     ((claps D).map (fun t=>invest (fun i=> ∑ y,enC F β H V U i (patchQ G y) • cry Y (F.seek i,y))
          (acts (exp (dg C)) (acts (exp (dg (W-C))) (changeM P x.2 (upMale L ho M)))) (fuelC F β H V U) t)).sum):=by
 intro α β Y' V U Z E W g d
 obtain ⟨l,f⟩:= cue_from x.2; let Y₀:= starfish N B x.2 l; have ht:=pose_g P he G hk w x p Y₀ (starK P.capY he.le p.cg f); let T:=Y.cap G hk (P.needed.trans w) M _ ht.glyph
 have hp:Sea α (graft G P x.1 M):=carts_sea (switchG G).symm T.projP (sea_g (P.clock_fine G w) x.1 p.fg _); let Q':= changeM P x.2 (upMale L ho M); let B':=hoist (patchQ G) (reefS G true) Q'
 have hy:TagG α Z:=tag_g _ (court G j L ho (Thread j) true M (T.chart true)).proj
 have hv:= voice he G hk w M x p Z hy d
 let e:= hv.1
 let sv (i:ι)(y:Single (CSide N B)):=enC F β E V U i (patchQ G y); let H(i:ι):=∑ y,sv i y • cry Y' (F.seek i,y); let r:= fuelC F β E V U
 have hx:TagG Y' W:=hv.1
 obtain ⟨t',Z'⟩:=rentF Y' W C T.projN hx g
 refine ⟨t',?_⟩
 let z:= Complex.exp (invoice (desire L j ho G M x Z))
 let y:=(sect0 G *chargeA (Thread j) G M (unionP x))⁻¹
 change y • pailL (patchQ G) (reefS G true) _= _; unfold effectK
 rw [show pailL _ _ _= (z * skyGlow B' V (graft G P x.1 M)) • acts (exp (dg W)) (((claps D).map (invest H Q' r)).sum) from forward _ _ (reefS_deck G true) T.projN (pierce G j L ho true M (unionP x)) F (court G j L ho (Thread j) true M (T.chart true)) hy d _ hp _ (sea_g w x.2 p.cg _) _, Complex.exp_add,charter G hk w x p he M, smul_smul]; rw [show (y*(z*skyGlow B' V (graft G P x.1 M)))= (y*skyGlow B' V (graft G P x.1 M))*z by rw [mul_comm z,mul_assoc]]; apply congrArg (fun k:Wave (Single (CSide N B))=>(y*skyGlow B' V (graft G P x.1 M)*z) • k)
 rw [map_list_sum,List.map_map]; change _=((claps D).map (fun t=> invest _ (acts _ _) _ t)).sum; congr 2; ext1 x
 change acts _ (offer _ x • chime _ _ x.term)=offer _ x • _
 rw [map_smul, chime, ←act_mul, show exp (dg W)*rollC H x.term= _ from (rams T.projN hx F.seek sv x.term).eq,act_mul,Z',act_mul]; rfl
end YM.CF.Proa
