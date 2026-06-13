-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = box.Text:upper()
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'xuBV2hfHXTtsl1wqVCl290cV'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-79DrtENpAn2L
return Vm.run(__src, { name = 'Build a ring farm/Build Ring A farm', checksum = 703594195, interval = 2, watermark = 'Y2k-79DrtENpAn2L', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
