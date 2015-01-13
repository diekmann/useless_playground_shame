' starts a script in the background
MsgBox "You are beeing monitored",0,"vbs"
Dim WinScriptHost
Set WinScriptHost = CreateObject("WScript.Shell")
WinScriptHost.Run Chr(34) & "C:\Users\...\file.bat" & Chr(34), 0
Set WinScriptHost = Nothing
