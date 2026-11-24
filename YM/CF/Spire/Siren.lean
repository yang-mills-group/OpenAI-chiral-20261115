import YM.CF.Spire.Elys
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {L m A B : Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e:ℝ} {P: Grasp Y B e}
variable (K:Pearl P)(w:Stamped j L o Y)(k:P.roundZ≤ (CSide m B).val)(p:1≤j)(G:Ratio (CSide m B) (CSide A B)) (h:G.count=L)
-- orientation-paid full step
abbrev altar(P:Grasp Y B e)(U:nomA m A B)(M:Tulip.Male):ℂ:= flakeL P G U M + candle m B (P.cost m (upMale L o M)) U.2 - candle A B (P.cost A M) U.1
abbrev salaryV(x:sewA m A B)(P:Grasp Y B e)(M:Tulip.Male):ℂ:= venture G P x M + candle m B (P.cost m (upMale L o M)) x.1.2 - candle A B (P.cost A M) x.1.1
include k h K
lemma penny (M:Tulip.Male)(x:nomA m A B)(g:JointB G x e)(l:0<e)(X:Stun (CSide m B))(s:Slow x.2 (hook X) K.r) : altar G P x M=salaryV G (accordL G x X) P M:=by
 obtain ⟨i,hx⟩:=cue_from (m:=m) x.2
 let A:= starfish m B x.2 i; have he := K.roof; have ht: Slow x.2 (hook A) K.q:=fun t l'=>(starK K.ample l.le g.cg hx t l').trans_le K.wide
 obtain ⟨Y,v,y⟩:=K.tick m x.2 g.cg A ht X (fun i j=>(s i j).trans_le K.wide)
 let f:= benchL P G x M
 have hu (m n)(v:glideV x.2 P.baseline m n): f m=f n:=by
    obtain ⟨p,hX,h0,h1,hG⟩:=v; have hd:(0:ℝ)∈ Set.Icc 0 1 :=⟨le_rfl,zero_le_one⟩
    have hx:ContinuousOn (fun i:ℝ=>f (p i)) (Set.Icc 0 1):=(bench_c P l G h k M).comp (f:=fun i=>(x,p i)) (continuousOn_const.prodMk hX) (fun i k=>⟨g,hG i k⟩)
    rw [←h0,←h1]; exact carry_log isPreconnected_Icc (v:=fun _=>f (p 0)) continuousOn_const hx 0 hd (fun a k'=> (chant_price P l G h k x g M _ (hG 0 hd)).trans (chant_price P l G h k x g M _ (hG a k')).symm) rfl _ ⟨zero_le_one,le_rfl⟩
 rw [altar, salaryV,flake_par P l G h k x g M _ hx]; rw [show benchL P G x M (starfish m B x.2 i)=venture G P (accordL G x X) M from (hu _ _ v).trans (hu _ _ y).symm]; rfl
lemma propel (z:sewA m A B)(p:Gild G z Y.e)(M:Tulip.Male) : Real.exp ((iExp j M G (post z)).trace.re/4)=‖coneP j M z.1.1 z.2.1‖ ∧ Real.exp ((fExp j L o M G (post z)).trace.re/4)= ‖coneP j (upMale L o M) z.1.2 z.2.2‖:=by
 let V:=Y.cap _ h (P.needed.trans k) M z p
 rw [V.lit,V.rod]; unfold coneP; constructor
 · rw [square_true,show foal j true M G _=boots G (spar j M z.1.1) from rfl]; unfold boots; rw [relabelF (switchG G).symm (C:= postC z.2.1) (starC (hook z.2.1 ∘ node) (fun i=> hookN ..)) V.projP,carts_n]
 rw [pierce,show skewE j (upMale L o M) true _ (post z).1.2=spar j (upMale L o M) z.1.2 from rfl,sec_salary G V.projN z,norm_smul,sectorU,one_mul, hoistN _ _ (reefS_deck ..)]
include p w
lemma wage_m(z:sewA m A B)(s:SectorK P G z)(M:Tulip.Male)(a:Shape)(b:Bool)(x:Slow z.1.1 (hook z.2.1) K.q)(y:Slow z.1.2 (hook z.2.2) K.q): salaryV G (lotX G a (xtra b) z) P M= cSignX (b.xor (detX a.s)) (salaryV G z P M):=by
 let H:=xtra b; let N:=upMale L o M
 let f:= P.cost A M; let g:= P.cost m N; let Y':= lotX G a H z; have hc:P.roundZ≤(CSide A B).val:=P.clock_fine G k
 let F:=fun x:sewA m A B=>((fExp j L o M G (post x)).trace.re/4); let I:=fun x:sewA m A B=>((iExp j M G (post x)).trace.re/4)
 let A':=fun z:sewA m A B=> ((F z):ℂ)+zen (hum m B g z.1.2 z.2.2); let B':=fun z:sewA m A B=> ((I z):ℂ)+zen (hum A B f z.1.1 z.2.1)
 let u:Sweep (CSide m B):=⟨a.s,wrap _ a.t,b⟩; let t:=detX a.s; let j':=b.xor t
 obtain ⟨U,hU⟩:=det_sub b a.s
 obtain ⟨l,r⟩:=propel K k G h z s.glyph M -- binder order
 have hv:Gild G Y' Y.e:=Vault.guild G z a H s.glyph; have hw:JointB G Y'.1 e:=alongS H a G z.1 _ s.cap; obtain ⟨v,W⟩:=propel K k G h Y' hv M
 have ha: F Y'= F z:= Real.exp_injective (W.trans ((chapelN K w k p z.2.2 z.1.2 s.cap.cg _ _ H U hU).trans r.symm))
 have hi: I Y'= I z:= Real.exp_injective (v.trans ((chapelN K w hc p z.2.1 z.1.1 s.cap.fg _ (Shape.broad G a) H U hU).trans l.symm))
 have hA:cSignX j' (A' z)=A' Y':=by unfold A'; rw [ley,ha]; congr 2; exact (humanity _ _ g z.1.2 z.2.2 a b).symm
 have hB:cSignX j' (B' z)=B' Y':=by unfold B'; rw [ley,hi]; congr 2; exact (humanity _ _ f z.1.1 z.2.1 (a.broad G) b).symm
 let L':=hireT j L o Y.n Y.k M G
 have hx(z:sewA m A B)(p':JointB G z.1 e)(u: Slow z.1.1 (hook z.2.1) K.q)(v:Slow z.1.2 (hook z.2.2) K.q) : salaryV G z P M=L' z + A' z-B' z:=by
   rw [salaryV,candleL K w k p _ p'.cg _ _ v,candleL K w hc p _ p'.fg M _ u, zen_a,zen_a]; unfold venture firmL bookL noteL L' hireT A' B' zen f g F I N; abel
 rw [show salaryV G (lotX G a (xtra b) z) _ _= _ from hx Y' hw (swayX (N:=CSide A B) H (Shape.broad G a) _ _ _ x) (swayX (N:=CSide m B) H a _ _ _ y), hx z s.cap x y]
 have hp:= w.blaze_X p M G h (P.needed.trans k) z s.glyph a H U hU
 rw [show L' Y'=cSignX j' (L' z) from hp,←hA,←hB]; change _=cSignX j' _; cases j'<;> simp [cSignX] -- tune
lemma chain_sym(l:0<e)(x:nomA m A B)(g:JointB G x e)(M:Tulip.Male)(a:Shape)(b:Bool): altar G P (stanza G a (xtra b) x) M= cSignX (b.xor (detX a.s)) (altar G P x M):=by
 let V:= x.2; obtain ⟨s,hx⟩:=cue_from (B:=B) (m:=m) x.2
 let S:=starfish m B V s
 have he: Slow V (hook S) K.r:=starK K.ample l.le g.cg hx
 let y:= stanza G a (xtra b) x; have hy:JointB G y e:= alongS _ _ G x _ g
 let z:= accordL G x S; let A':= lotX G a (xtra b) z; let X:= fume (xtra b) a S; have ht: Slow y.2 (hook X) K.r:=swayX (N:=CSide m B) (xtra b) _ _ S _ he
 let v:=accordL G y X; have hv: Slow x.1 (hook z.2.1) K.q:= Pearl.liftR K G h x S l k g he
 rw [show stanza _ _ _ x=y from rfl,penny K k G h M y hy l X ht,penny K k G h M x g l S he,← wage_m K w k p G h z (pose_g P l G h k x g S (fun i j=>(he i j).trans_le (K.wide.trans K.roof))) M a b hv (fun i j=>(he i j).trans_le K.wide)] -- tune A
 obtain ⟨hL,hB⟩:= mare_L K G h y A'.2.1 v.2.1 X (equip_x G z (equip_p G x S) a _) (equip_p G y X) hy (swayX (N:=CSide A B) _ (a.broad G) x.1 _ _ hv) (K.liftR G h _ _ l k hy ht) (fun i j=>(ht i j).trans_le K.wide)
 have hk:=worth (P:=P) k G h y _ X M hL hB; rw [mare_l,mare_r] at hk; unfold salaryV; rw [show venture G P (accordL G y X) M=venture G P A' M from hk.symm]; rfl
end YM.CF.Spire
